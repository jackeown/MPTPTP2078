%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:14 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  334 (20936 expanded)
%              Number of clauses        :  215 (4518 expanded)
%              Number of leaves         :   28 (5848 expanded)
%              Depth                    :   38
%              Number of atoms          : 1863 (190405 expanded)
%              Number of equality atoms :  367 (6998 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f70,plain,(
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
    inference(flattening,[],[f69])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK6)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK6) )
        & ( r1_waybel_7(X0,X1,sK6)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK6) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
            ( ( ~ r1_waybel_7(X0,sK5,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK5),X2) )
            & ( r1_waybel_7(X0,sK5,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK5),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
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
              ( ( ~ r1_waybel_7(sK4,X1,X2)
                | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X1),X2) )
              & ( r1_waybel_7(sK4,X1,X2)
                | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK4)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK4)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ( ~ r1_waybel_7(sK4,sK5,sK6)
      | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) )
    & ( r1_waybel_7(sK4,sK5,sK6)
      | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    & ~ v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f70,f73,f72,f71])).

fof(f113,plain,(
    v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f74])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f128,plain,(
    v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(definition_unfolding,[],[f113,f91])).

fof(f15,axiom,(
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

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f120,plain,(
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
    inference(definition_unfolding,[],[f99,f91,f91,f91])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f74])).

fof(f108,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

fof(f114,plain,(
    v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f74])).

fof(f127,plain,(
    v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(definition_unfolding,[],[f114,f91])).

fof(f111,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f115,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) ),
    inference(cnf_transformation,[],[f74])).

fof(f126,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
    inference(definition_unfolding,[],[f115,f91])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
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
    inference(definition_unfolding,[],[f100,f91,f91,f91])).

fof(f118,plain,
    ( ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f18,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f106,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f109,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f74])).

fof(f116,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f74])).

fof(f19,axiom,(
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

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f107,f91,f91,f91,f91])).

fof(f112,plain,(
    v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f74])).

fof(f129,plain,(
    v1_subset_1(sK5,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))) ),
    inference(definition_unfolding,[],[f112,f91])).

fof(f117,plain,
    ( r1_waybel_7(sK4,sK5,sK6)
    | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f105,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f25,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
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
    inference(definition_unfolding,[],[f102,f91,f91,f91])).

fof(f17,axiom,(
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

fof(f23,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f123,plain,(
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
    inference(definition_unfolding,[],[f104,f91,f91,f91,f91])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v7_struct_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( X1 = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK3(X0) != X1
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK2(X0) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ( sK2(X0) != sK3(X0)
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f64,f66,f65])).

fof(f97,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | sK2(X0) != sK3(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0))
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f95,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f93,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_37,negated_conjecture,
    ( v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_24,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1008,plain,
    ( l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_40])).

cnf(c_1009,plain,
    ( l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1008])).

cnf(c_1977,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_1009])).

cnf(c_1978,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
    | v2_struct_0(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1977])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1982,plain,
    ( ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1978,c_42])).

cnf(c_1983,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1982])).

cnf(c_36,negated_conjecture,
    ( v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2483,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1983,c_36])).

cnf(c_2484,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2483])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2488,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2484,c_39])).

cnf(c_2489,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2488])).

cnf(c_3036,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_2489])).

cnf(c_3488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_3036])).

cnf(c_4710,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,X0,sK5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3488])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1867,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_1009])).

cnf(c_1868,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1867])).

cnf(c_4836,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,X0,sK5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4710,c_1868])).

cnf(c_5497,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4836])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_23,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_32,negated_conjecture,
    ( ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_339,plain,
    ( ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_32])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f106])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_930,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_931,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_935,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_42,c_40])).

cnf(c_1400,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != X0
    | sK6 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_935])).

cnf(c_1401,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(unflattening,[status(thm)],[c_1400])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1403,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1401,c_34])).

cnf(c_1404,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(renaming,[status(thm)],[c_1403])).

cnf(c_1440,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(X2,X1,X0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1404])).

cnf(c_1441,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1440])).

cnf(c_116,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1445,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_42,c_40,c_116])).

cnf(c_2588,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1445,c_36])).

cnf(c_2589,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2588])).

cnf(c_2593,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2589,c_39])).

cnf(c_2594,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2593])).

cnf(c_2937,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_2594])).

cnf(c_3500,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2937])).

cnf(c_4199,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ r1_waybel_7(sK4,sK5,sK6)
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3500])).

cnf(c_4705,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6) != iProver_top
    | r1_waybel_7(sK4,sK5,sK6) != iProver_top
    | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4199])).

cnf(c_31,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_38,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_611,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_38])).

cnf(c_612,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK5)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_616,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_39])).

cnf(c_617,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_616])).

cnf(c_1798,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_617,c_1009])).

cnf(c_1799,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
    | v2_struct_0(sK4)
    | k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = sK5
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_1798])).

cnf(c_1801,plain,
    ( k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = sK5
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1799,c_42,c_37,c_36,c_35])).

cnf(c_3515,plain,
    ( k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_1801])).

cnf(c_4885,plain,
    ( r1_waybel_7(sK4,sK5,sK6) != iProver_top
    | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4705,c_3515])).

cnf(c_33,negated_conjecture,
    ( r1_waybel_7(sK4,sK5,sK6)
    | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_341,plain,
    ( r1_waybel_7(sK4,sK5,sK6)
    | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f105])).

cnf(c_897,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_898,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | ~ r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_897])).

cnf(c_902,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | ~ r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_898,c_42,c_40])).

cnf(c_1374,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != X0
    | sK6 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_341,c_902])).

cnf(c_1375,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(unflattening,[status(thm)],[c_1374])).

cnf(c_1377,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | r1_waybel_7(sK4,sK5,sK6)
    | r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1375,c_34])).

cnf(c_1378,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(renaming,[status(thm)],[c_1377])).

cnf(c_1488,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(X2,X1,X0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1378])).

cnf(c_1489,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1488])).

cnf(c_1493,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1489,c_42,c_40,c_116])).

cnf(c_2543,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1493,c_36])).

cnf(c_2544,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2543])).

cnf(c_2548,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK4,sK5,sK6)
    | r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2544,c_39])).

cnf(c_2549,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2548])).

cnf(c_2975,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_2549])).

cnf(c_3496,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2975])).

cnf(c_4200,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
    | r1_waybel_7(sK4,sK5,sK6)
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3496])).

cnf(c_4707,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6) = iProver_top
    | r1_waybel_7(sK4,sK5,sK6) = iProver_top
    | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4200])).

cnf(c_4861,plain,
    ( r1_waybel_7(sK4,sK5,sK6) = iProver_top
    | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4707,c_3515])).

cnf(c_4891,plain,
    ( v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4885,c_4861])).

cnf(c_4204,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5318,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) = k3_lattice3(k1_lattice3(k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_4204])).

cnf(c_4198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3500])).

cnf(c_4706,plain,
    ( k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4198])).

cnf(c_4847,plain,
    ( k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4706,c_1868])).

cnf(c_5730,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(k2_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4847])).

cnf(c_25,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1944,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1009])).

cnf(c_1945,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_orders_2(k3_yellow19(sK4,X1,X0))
    | v2_struct_0(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1944])).

cnf(c_1949,plain,
    ( v4_orders_2(k3_yellow19(sK4,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1945,c_42])).

cnf(c_1950,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_orders_2(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1949])).

cnf(c_2513,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_orders_2(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1950,c_36])).

cnf(c_2514,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2513])).

cnf(c_2518,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK4,X0,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2514,c_39])).

cnf(c_2519,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2518])).

cnf(c_3013,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_2519])).

cnf(c_3492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_3013])).

cnf(c_4709,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3492])).

cnf(c_4825,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4709,c_1868])).

cnf(c_5828,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4825])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f123])).

cnf(c_572,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_573,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK5))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_577,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_39])).

cnf(c_578,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK5))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_577])).

cnf(c_1872,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK5))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_578,c_1009])).

cnf(c_1873,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
    | v2_struct_0(sK4)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1872])).

cnf(c_1877,plain,
    ( v7_waybel_0(k3_yellow19(sK4,X0,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1873,c_42])).

cnf(c_1878,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1877])).

cnf(c_2633,plain,
    ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1878])).

cnf(c_2911,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_2633])).

cnf(c_3504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2911])).

cnf(c_4704,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3504])).

cnf(c_4872,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4704,c_1868])).

cnf(c_5887,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(k2_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4872])).

cnf(c_6259,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_50,c_4891,c_5318,c_5730,c_5828,c_5887])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4726,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4741,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4726,c_7])).

cnf(c_6265,plain,
    ( v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6259,c_4741])).

cnf(c_20,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0))
    | v7_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1819,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0))
    | v7_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1009])).

cnf(c_1820,plain,
    ( m1_subset_1(sK3(sK4),u1_struct_0(sK4))
    | v7_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1819])).

cnf(c_4716,plain,
    ( m1_subset_1(sK3(sK4),u1_struct_0(sK4)) = iProver_top
    | v7_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_4756,plain,
    ( m1_subset_1(sK3(sK4),k2_struct_0(sK4)) = iProver_top
    | v7_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4716,c_1868])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4727,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5735,plain,
    ( v7_struct_0(sK4) = iProver_top
    | v1_xboole_0(sK3(sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4756,c_4727])).

cnf(c_45,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_19,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | sK3(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_88,plain,
    ( sK3(X0) != sK2(X0)
    | v7_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_90,plain,
    ( sK3(sK4) != sK2(sK4)
    | v7_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_115,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_117,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5667,plain,
    ( ~ v1_xboole_0(sK3(sK4))
    | ~ v1_xboole_0(sK2(sK4))
    | sK3(sK4) = sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5671,plain,
    ( sK3(sK4) = sK2(sK4)
    | v1_xboole_0(sK3(sK4)) != iProver_top
    | v1_xboole_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5667])).

cnf(c_21,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | v7_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1809,plain,
    ( m1_subset_1(sK2(X0),u1_struct_0(X0))
    | v7_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1009])).

cnf(c_1810,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4))
    | v7_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1809])).

cnf(c_4717,plain,
    ( m1_subset_1(sK2(sK4),u1_struct_0(sK4)) = iProver_top
    | v7_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_4761,plain,
    ( m1_subset_1(sK2(sK4),k2_struct_0(sK4)) = iProver_top
    | v7_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4717,c_1868])).

cnf(c_5812,plain,
    ( v7_struct_0(sK4) = iProver_top
    | v1_xboole_0(sK2(sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4761,c_4727])).

cnf(c_6096,plain,
    ( v7_struct_0(sK4) = iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5735,c_45,c_90,c_117,c_5671,c_5812])).

cnf(c_6269,plain,
    ( v7_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_6096])).

cnf(c_18,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1839,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1009])).

cnf(c_1840,plain,
    ( m1_subset_1(sK1(sK4),u1_struct_0(sK4))
    | ~ v7_struct_0(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1839])).

cnf(c_1842,plain,
    ( ~ v7_struct_0(sK4)
    | m1_subset_1(sK1(sK4),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1840,c_42])).

cnf(c_1843,plain,
    ( m1_subset_1(sK1(sK4),u1_struct_0(sK4))
    | ~ v7_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_1842])).

cnf(c_4714,plain,
    ( m1_subset_1(sK1(sK4),u1_struct_0(sK4)) = iProver_top
    | v7_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1843])).

cnf(c_4766,plain,
    ( m1_subset_1(sK1(sK4),k2_struct_0(sK4)) = iProver_top
    | v7_struct_0(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4714,c_1868])).

cnf(c_4725,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4738,plain,
    ( m1_subset_1(sK6,k2_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4725,c_1868])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1905,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | X0 = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1009])).

cnf(c_1906,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v7_struct_0(sK4)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1905])).

cnf(c_4712,plain,
    ( X0 = X1
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | v7_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1906])).

cnf(c_4815,plain,
    ( X0 = X1
    | m1_subset_1(X1,k2_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
    | v7_struct_0(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4712,c_1868])).

cnf(c_5379,plain,
    ( sK6 = X0
    | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
    | v7_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4738,c_4815])).

cnf(c_5416,plain,
    ( sK1(sK4) = sK6
    | v7_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4766,c_5379])).

cnf(c_6527,plain,
    ( sK1(sK4) = sK6 ),
    inference(superposition,[status(thm)],[c_6269,c_5416])).

cnf(c_5174,plain,
    ( v1_xboole_0(k2_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4738,c_4727])).

cnf(c_6273,plain,
    ( v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_5174])).

cnf(c_4729,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6267,plain,
    ( k2_struct_0(sK4) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_4729])).

cnf(c_6382,plain,
    ( k2_struct_0(sK4) = sK6 ),
    inference(superposition,[status(thm)],[c_6273,c_6267])).

cnf(c_17,plain,
    ( ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK1(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1853,plain,
    ( ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK1(X0)) = u1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1009])).

cnf(c_1854,plain,
    ( ~ v7_struct_0(sK4)
    | v2_struct_0(sK4)
    | k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1853])).

cnf(c_95,plain,
    ( ~ v7_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1856,plain,
    ( ~ v7_struct_0(sK4)
    | k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1854,c_42,c_40,c_95,c_116])).

cnf(c_4713,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4)
    | v7_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1856])).

cnf(c_4771,plain,
    ( k6_domain_1(k2_struct_0(sK4),sK1(sK4)) = k2_struct_0(sK4)
    | v7_struct_0(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4713,c_1868])).

cnf(c_6554,plain,
    ( k6_domain_1(sK6,sK1(sK4)) = sK6
    | v7_struct_0(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6382,c_4771])).

cnf(c_6948,plain,
    ( k6_domain_1(sK6,sK1(sK4)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6554,c_6096,c_6265])).

cnf(c_7612,plain,
    ( k6_domain_1(sK6,sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_6527,c_6948])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_11])).

cnf(c_261,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_13,plain,
    ( ~ m2_connsp_2(X0,X1,k6_domain_1(u1_struct_0(X1),X2))
    | m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_14,plain,
    ( m2_connsp_2(k2_struct_0(X0),X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_663,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | X4 != X1
    | k6_domain_1(u1_struct_0(X1),X2) != X3
    | k2_struct_0(X4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_664,plain,
    ( m1_connsp_2(k2_struct_0(X0),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X3),X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
    | r2_hidden(X0,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | k2_struct_0(X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_664])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_963,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_777,c_41])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,k2_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_963])).

cnf(c_968,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,k2_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_964,c_42,c_40])).

cnf(c_1049,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(X1)
    | X0 != X2
    | k2_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_968])).

cnf(c_1050,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(k2_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1049])).

cnf(c_4201,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1050])).

cnf(c_4719,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4201])).

cnf(c_4808,plain,
    ( m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
    | m1_subset_1(k6_domain_1(k2_struct_0(sK4),X0),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4719,c_1868])).

cnf(c_6552,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(k6_domain_1(sK6,X0),k1_zfmisc_1(sK6)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_6382,c_4808])).

cnf(c_4202,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(k2_struct_0(sK4))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1050])).

cnf(c_4718,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4202])).

cnf(c_4794,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4718,c_1868])).

cnf(c_4798,plain,
    ( v1_xboole_0(k2_struct_0(sK4)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4794,c_4741])).

cnf(c_7059,plain,
    ( m1_subset_1(k6_domain_1(sK6,X0),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6552,c_4798,c_6265])).

cnf(c_7060,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(k6_domain_1(sK6,X0),k1_zfmisc_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7059])).

cnf(c_7617,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7612,c_7060])).

cnf(c_6557,plain,
    ( m1_subset_1(sK1(sK4),sK6) = iProver_top
    | v7_struct_0(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6382,c_4766])).

cnf(c_7068,plain,
    ( m1_subset_1(sK1(sK4),sK6) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6948,c_7060])).

cnf(c_7792,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7617,c_6096,c_6265,c_6557,c_7068])).

cnf(c_7797,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7792,c_4741])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.00/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.02  
% 3.00/1.02  ------  iProver source info
% 3.00/1.02  
% 3.00/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.02  git: non_committed_changes: false
% 3.00/1.02  git: last_make_outside_of_git: false
% 3.00/1.02  
% 3.00/1.02  ------ 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options
% 3.00/1.02  
% 3.00/1.02  --out_options                           all
% 3.00/1.02  --tptp_safe_out                         true
% 3.00/1.02  --problem_path                          ""
% 3.00/1.02  --include_path                          ""
% 3.00/1.02  --clausifier                            res/vclausify_rel
% 3.00/1.02  --clausifier_options                    --mode clausify
% 3.00/1.02  --stdin                                 false
% 3.00/1.02  --stats_out                             all
% 3.00/1.02  
% 3.00/1.02  ------ General Options
% 3.00/1.02  
% 3.00/1.02  --fof                                   false
% 3.00/1.02  --time_out_real                         305.
% 3.00/1.02  --time_out_virtual                      -1.
% 3.00/1.02  --symbol_type_check                     false
% 3.00/1.02  --clausify_out                          false
% 3.00/1.02  --sig_cnt_out                           false
% 3.00/1.02  --trig_cnt_out                          false
% 3.00/1.02  --trig_cnt_out_tolerance                1.
% 3.00/1.02  --trig_cnt_out_sk_spl                   false
% 3.00/1.02  --abstr_cl_out                          false
% 3.00/1.02  
% 3.00/1.02  ------ Global Options
% 3.00/1.02  
% 3.00/1.02  --schedule                              default
% 3.00/1.02  --add_important_lit                     false
% 3.00/1.02  --prop_solver_per_cl                    1000
% 3.00/1.02  --min_unsat_core                        false
% 3.00/1.02  --soft_assumptions                      false
% 3.00/1.02  --soft_lemma_size                       3
% 3.00/1.02  --prop_impl_unit_size                   0
% 3.00/1.02  --prop_impl_unit                        []
% 3.00/1.02  --share_sel_clauses                     true
% 3.00/1.02  --reset_solvers                         false
% 3.00/1.02  --bc_imp_inh                            [conj_cone]
% 3.00/1.02  --conj_cone_tolerance                   3.
% 3.00/1.02  --extra_neg_conj                        none
% 3.00/1.02  --large_theory_mode                     true
% 3.00/1.02  --prolific_symb_bound                   200
% 3.00/1.02  --lt_threshold                          2000
% 3.00/1.02  --clause_weak_htbl                      true
% 3.00/1.02  --gc_record_bc_elim                     false
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing Options
% 3.00/1.02  
% 3.00/1.02  --preprocessing_flag                    true
% 3.00/1.02  --time_out_prep_mult                    0.1
% 3.00/1.02  --splitting_mode                        input
% 3.00/1.02  --splitting_grd                         true
% 3.00/1.02  --splitting_cvd                         false
% 3.00/1.02  --splitting_cvd_svl                     false
% 3.00/1.02  --splitting_nvd                         32
% 3.00/1.02  --sub_typing                            true
% 3.00/1.02  --prep_gs_sim                           true
% 3.00/1.02  --prep_unflatten                        true
% 3.00/1.02  --prep_res_sim                          true
% 3.00/1.02  --prep_upred                            true
% 3.00/1.02  --prep_sem_filter                       exhaustive
% 3.00/1.02  --prep_sem_filter_out                   false
% 3.00/1.02  --pred_elim                             true
% 3.00/1.02  --res_sim_input                         true
% 3.00/1.02  --eq_ax_congr_red                       true
% 3.00/1.02  --pure_diseq_elim                       true
% 3.00/1.02  --brand_transform                       false
% 3.00/1.02  --non_eq_to_eq                          false
% 3.00/1.02  --prep_def_merge                        true
% 3.00/1.02  --prep_def_merge_prop_impl              false
% 3.00/1.02  --prep_def_merge_mbd                    true
% 3.00/1.02  --prep_def_merge_tr_red                 false
% 3.00/1.02  --prep_def_merge_tr_cl                  false
% 3.00/1.02  --smt_preprocessing                     true
% 3.00/1.02  --smt_ac_axioms                         fast
% 3.00/1.02  --preprocessed_out                      false
% 3.00/1.02  --preprocessed_stats                    false
% 3.00/1.02  
% 3.00/1.02  ------ Abstraction refinement Options
% 3.00/1.02  
% 3.00/1.02  --abstr_ref                             []
% 3.00/1.02  --abstr_ref_prep                        false
% 3.00/1.02  --abstr_ref_until_sat                   false
% 3.00/1.02  --abstr_ref_sig_restrict                funpre
% 3.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.02  --abstr_ref_under                       []
% 3.00/1.02  
% 3.00/1.02  ------ SAT Options
% 3.00/1.02  
% 3.00/1.02  --sat_mode                              false
% 3.00/1.02  --sat_fm_restart_options                ""
% 3.00/1.02  --sat_gr_def                            false
% 3.00/1.02  --sat_epr_types                         true
% 3.00/1.02  --sat_non_cyclic_types                  false
% 3.00/1.02  --sat_finite_models                     false
% 3.00/1.02  --sat_fm_lemmas                         false
% 3.00/1.02  --sat_fm_prep                           false
% 3.00/1.02  --sat_fm_uc_incr                        true
% 3.00/1.02  --sat_out_model                         small
% 3.00/1.02  --sat_out_clauses                       false
% 3.00/1.02  
% 3.00/1.02  ------ QBF Options
% 3.00/1.02  
% 3.00/1.02  --qbf_mode                              false
% 3.00/1.02  --qbf_elim_univ                         false
% 3.00/1.02  --qbf_dom_inst                          none
% 3.00/1.02  --qbf_dom_pre_inst                      false
% 3.00/1.02  --qbf_sk_in                             false
% 3.00/1.02  --qbf_pred_elim                         true
% 3.00/1.02  --qbf_split                             512
% 3.00/1.02  
% 3.00/1.02  ------ BMC1 Options
% 3.00/1.02  
% 3.00/1.02  --bmc1_incremental                      false
% 3.00/1.02  --bmc1_axioms                           reachable_all
% 3.00/1.02  --bmc1_min_bound                        0
% 3.00/1.02  --bmc1_max_bound                        -1
% 3.00/1.02  --bmc1_max_bound_default                -1
% 3.00/1.02  --bmc1_symbol_reachability              true
% 3.00/1.02  --bmc1_property_lemmas                  false
% 3.00/1.02  --bmc1_k_induction                      false
% 3.00/1.02  --bmc1_non_equiv_states                 false
% 3.00/1.02  --bmc1_deadlock                         false
% 3.00/1.02  --bmc1_ucm                              false
% 3.00/1.02  --bmc1_add_unsat_core                   none
% 3.00/1.02  --bmc1_unsat_core_children              false
% 3.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.02  --bmc1_out_stat                         full
% 3.00/1.02  --bmc1_ground_init                      false
% 3.00/1.02  --bmc1_pre_inst_next_state              false
% 3.00/1.02  --bmc1_pre_inst_state                   false
% 3.00/1.02  --bmc1_pre_inst_reach_state             false
% 3.00/1.02  --bmc1_out_unsat_core                   false
% 3.00/1.02  --bmc1_aig_witness_out                  false
% 3.00/1.02  --bmc1_verbose                          false
% 3.00/1.02  --bmc1_dump_clauses_tptp                false
% 3.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.02  --bmc1_dump_file                        -
% 3.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.02  --bmc1_ucm_extend_mode                  1
% 3.00/1.02  --bmc1_ucm_init_mode                    2
% 3.00/1.02  --bmc1_ucm_cone_mode                    none
% 3.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.02  --bmc1_ucm_relax_model                  4
% 3.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.02  --bmc1_ucm_layered_model                none
% 3.00/1.02  --bmc1_ucm_max_lemma_size               10
% 3.00/1.02  
% 3.00/1.02  ------ AIG Options
% 3.00/1.02  
% 3.00/1.02  --aig_mode                              false
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation Options
% 3.00/1.02  
% 3.00/1.02  --instantiation_flag                    true
% 3.00/1.02  --inst_sos_flag                         false
% 3.00/1.02  --inst_sos_phase                        true
% 3.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel_side                     num_symb
% 3.00/1.02  --inst_solver_per_active                1400
% 3.00/1.02  --inst_solver_calls_frac                1.
% 3.00/1.02  --inst_passive_queue_type               priority_queues
% 3.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.02  --inst_passive_queues_freq              [25;2]
% 3.00/1.02  --inst_dismatching                      true
% 3.00/1.02  --inst_eager_unprocessed_to_passive     true
% 3.00/1.02  --inst_prop_sim_given                   true
% 3.00/1.02  --inst_prop_sim_new                     false
% 3.00/1.02  --inst_subs_new                         false
% 3.00/1.02  --inst_eq_res_simp                      false
% 3.00/1.02  --inst_subs_given                       false
% 3.00/1.02  --inst_orphan_elimination               true
% 3.00/1.02  --inst_learning_loop_flag               true
% 3.00/1.02  --inst_learning_start                   3000
% 3.00/1.02  --inst_learning_factor                  2
% 3.00/1.02  --inst_start_prop_sim_after_learn       3
% 3.00/1.02  --inst_sel_renew                        solver
% 3.00/1.02  --inst_lit_activity_flag                true
% 3.00/1.02  --inst_restr_to_given                   false
% 3.00/1.02  --inst_activity_threshold               500
% 3.00/1.02  --inst_out_proof                        true
% 3.00/1.02  
% 3.00/1.02  ------ Resolution Options
% 3.00/1.02  
% 3.00/1.02  --resolution_flag                       true
% 3.00/1.02  --res_lit_sel                           adaptive
% 3.00/1.02  --res_lit_sel_side                      none
% 3.00/1.02  --res_ordering                          kbo
% 3.00/1.02  --res_to_prop_solver                    active
% 3.00/1.02  --res_prop_simpl_new                    false
% 3.00/1.02  --res_prop_simpl_given                  true
% 3.00/1.02  --res_passive_queue_type                priority_queues
% 3.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.02  --res_passive_queues_freq               [15;5]
% 3.00/1.02  --res_forward_subs                      full
% 3.00/1.02  --res_backward_subs                     full
% 3.00/1.02  --res_forward_subs_resolution           true
% 3.00/1.02  --res_backward_subs_resolution          true
% 3.00/1.02  --res_orphan_elimination                true
% 3.00/1.02  --res_time_limit                        2.
% 3.00/1.02  --res_out_proof                         true
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Options
% 3.00/1.02  
% 3.00/1.02  --superposition_flag                    true
% 3.00/1.02  --sup_passive_queue_type                priority_queues
% 3.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.02  --demod_completeness_check              fast
% 3.00/1.02  --demod_use_ground                      true
% 3.00/1.02  --sup_to_prop_solver                    passive
% 3.00/1.02  --sup_prop_simpl_new                    true
% 3.00/1.02  --sup_prop_simpl_given                  true
% 3.00/1.02  --sup_fun_splitting                     false
% 3.00/1.02  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  ------ Parsing...
% 3.00/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.02  ------ Proving...
% 3.00/1.02  ------ Problem Properties 
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  clauses                                 29
% 3.00/1.02  conjectures                             4
% 3.00/1.02  EPR                                     5
% 3.00/1.02  Horn                                    22
% 3.00/1.02  unary                                   8
% 3.00/1.02  binary                                  6
% 3.00/1.02  lits                                    86
% 3.00/1.02  lits eq                                 16
% 3.00/1.02  fd_pure                                 0
% 3.00/1.02  fd_pseudo                               0
% 3.00/1.02  fd_cond                                 0
% 3.00/1.02  fd_pseudo_cond                          2
% 3.00/1.02  AC symbols                              0
% 3.00/1.02  
% 3.00/1.02  ------ Schedule dynamic 5 is on 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ 
% 3.00/1.02  Current options:
% 3.00/1.02  ------ 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options
% 3.00/1.02  
% 3.00/1.02  --out_options                           all
% 3.00/1.02  --tptp_safe_out                         true
% 3.00/1.02  --problem_path                          ""
% 3.00/1.02  --include_path                          ""
% 3.00/1.02  --clausifier                            res/vclausify_rel
% 3.00/1.02  --clausifier_options                    --mode clausify
% 3.00/1.02  --stdin                                 false
% 3.00/1.02  --stats_out                             all
% 3.00/1.02  
% 3.00/1.02  ------ General Options
% 3.00/1.02  
% 3.00/1.02  --fof                                   false
% 3.00/1.02  --time_out_real                         305.
% 3.00/1.02  --time_out_virtual                      -1.
% 3.00/1.02  --symbol_type_check                     false
% 3.00/1.02  --clausify_out                          false
% 3.00/1.02  --sig_cnt_out                           false
% 3.00/1.02  --trig_cnt_out                          false
% 3.00/1.02  --trig_cnt_out_tolerance                1.
% 3.00/1.02  --trig_cnt_out_sk_spl                   false
% 3.00/1.02  --abstr_cl_out                          false
% 3.00/1.02  
% 3.00/1.02  ------ Global Options
% 3.00/1.02  
% 3.00/1.02  --schedule                              default
% 3.00/1.02  --add_important_lit                     false
% 3.00/1.02  --prop_solver_per_cl                    1000
% 3.00/1.02  --min_unsat_core                        false
% 3.00/1.02  --soft_assumptions                      false
% 3.00/1.02  --soft_lemma_size                       3
% 3.00/1.02  --prop_impl_unit_size                   0
% 3.00/1.02  --prop_impl_unit                        []
% 3.00/1.02  --share_sel_clauses                     true
% 3.00/1.02  --reset_solvers                         false
% 3.00/1.02  --bc_imp_inh                            [conj_cone]
% 3.00/1.02  --conj_cone_tolerance                   3.
% 3.00/1.02  --extra_neg_conj                        none
% 3.00/1.02  --large_theory_mode                     true
% 3.00/1.02  --prolific_symb_bound                   200
% 3.00/1.02  --lt_threshold                          2000
% 3.00/1.02  --clause_weak_htbl                      true
% 3.00/1.02  --gc_record_bc_elim                     false
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing Options
% 3.00/1.02  
% 3.00/1.02  --preprocessing_flag                    true
% 3.00/1.02  --time_out_prep_mult                    0.1
% 3.00/1.02  --splitting_mode                        input
% 3.00/1.02  --splitting_grd                         true
% 3.00/1.02  --splitting_cvd                         false
% 3.00/1.02  --splitting_cvd_svl                     false
% 3.00/1.02  --splitting_nvd                         32
% 3.00/1.02  --sub_typing                            true
% 3.00/1.02  --prep_gs_sim                           true
% 3.00/1.02  --prep_unflatten                        true
% 3.00/1.02  --prep_res_sim                          true
% 3.00/1.02  --prep_upred                            true
% 3.00/1.02  --prep_sem_filter                       exhaustive
% 3.00/1.02  --prep_sem_filter_out                   false
% 3.00/1.02  --pred_elim                             true
% 3.00/1.02  --res_sim_input                         true
% 3.00/1.02  --eq_ax_congr_red                       true
% 3.00/1.02  --pure_diseq_elim                       true
% 3.00/1.02  --brand_transform                       false
% 3.00/1.02  --non_eq_to_eq                          false
% 3.00/1.02  --prep_def_merge                        true
% 3.00/1.02  --prep_def_merge_prop_impl              false
% 3.00/1.02  --prep_def_merge_mbd                    true
% 3.00/1.02  --prep_def_merge_tr_red                 false
% 3.00/1.02  --prep_def_merge_tr_cl                  false
% 3.00/1.02  --smt_preprocessing                     true
% 3.00/1.02  --smt_ac_axioms                         fast
% 3.00/1.02  --preprocessed_out                      false
% 3.00/1.02  --preprocessed_stats                    false
% 3.00/1.02  
% 3.00/1.02  ------ Abstraction refinement Options
% 3.00/1.02  
% 3.00/1.02  --abstr_ref                             []
% 3.00/1.02  --abstr_ref_prep                        false
% 3.00/1.02  --abstr_ref_until_sat                   false
% 3.00/1.02  --abstr_ref_sig_restrict                funpre
% 3.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.02  --abstr_ref_under                       []
% 3.00/1.02  
% 3.00/1.02  ------ SAT Options
% 3.00/1.02  
% 3.00/1.02  --sat_mode                              false
% 3.00/1.02  --sat_fm_restart_options                ""
% 3.00/1.02  --sat_gr_def                            false
% 3.00/1.02  --sat_epr_types                         true
% 3.00/1.02  --sat_non_cyclic_types                  false
% 3.00/1.02  --sat_finite_models                     false
% 3.00/1.02  --sat_fm_lemmas                         false
% 3.00/1.02  --sat_fm_prep                           false
% 3.00/1.02  --sat_fm_uc_incr                        true
% 3.00/1.02  --sat_out_model                         small
% 3.00/1.02  --sat_out_clauses                       false
% 3.00/1.02  
% 3.00/1.02  ------ QBF Options
% 3.00/1.02  
% 3.00/1.02  --qbf_mode                              false
% 3.00/1.02  --qbf_elim_univ                         false
% 3.00/1.02  --qbf_dom_inst                          none
% 3.00/1.02  --qbf_dom_pre_inst                      false
% 3.00/1.02  --qbf_sk_in                             false
% 3.00/1.02  --qbf_pred_elim                         true
% 3.00/1.02  --qbf_split                             512
% 3.00/1.02  
% 3.00/1.02  ------ BMC1 Options
% 3.00/1.02  
% 3.00/1.02  --bmc1_incremental                      false
% 3.00/1.02  --bmc1_axioms                           reachable_all
% 3.00/1.02  --bmc1_min_bound                        0
% 3.00/1.02  --bmc1_max_bound                        -1
% 3.00/1.02  --bmc1_max_bound_default                -1
% 3.00/1.02  --bmc1_symbol_reachability              true
% 3.00/1.02  --bmc1_property_lemmas                  false
% 3.00/1.02  --bmc1_k_induction                      false
% 3.00/1.02  --bmc1_non_equiv_states                 false
% 3.00/1.02  --bmc1_deadlock                         false
% 3.00/1.02  --bmc1_ucm                              false
% 3.00/1.02  --bmc1_add_unsat_core                   none
% 3.00/1.02  --bmc1_unsat_core_children              false
% 3.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.02  --bmc1_out_stat                         full
% 3.00/1.02  --bmc1_ground_init                      false
% 3.00/1.02  --bmc1_pre_inst_next_state              false
% 3.00/1.02  --bmc1_pre_inst_state                   false
% 3.00/1.02  --bmc1_pre_inst_reach_state             false
% 3.00/1.02  --bmc1_out_unsat_core                   false
% 3.00/1.02  --bmc1_aig_witness_out                  false
% 3.00/1.02  --bmc1_verbose                          false
% 3.00/1.02  --bmc1_dump_clauses_tptp                false
% 3.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.02  --bmc1_dump_file                        -
% 3.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.02  --bmc1_ucm_extend_mode                  1
% 3.00/1.02  --bmc1_ucm_init_mode                    2
% 3.00/1.02  --bmc1_ucm_cone_mode                    none
% 3.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.02  --bmc1_ucm_relax_model                  4
% 3.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.02  --bmc1_ucm_layered_model                none
% 3.00/1.02  --bmc1_ucm_max_lemma_size               10
% 3.00/1.02  
% 3.00/1.02  ------ AIG Options
% 3.00/1.02  
% 3.00/1.02  --aig_mode                              false
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation Options
% 3.00/1.02  
% 3.00/1.02  --instantiation_flag                    true
% 3.00/1.02  --inst_sos_flag                         false
% 3.00/1.02  --inst_sos_phase                        true
% 3.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel_side                     none
% 3.00/1.02  --inst_solver_per_active                1400
% 3.00/1.02  --inst_solver_calls_frac                1.
% 3.00/1.02  --inst_passive_queue_type               priority_queues
% 3.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.02  --inst_passive_queues_freq              [25;2]
% 3.00/1.02  --inst_dismatching                      true
% 3.00/1.02  --inst_eager_unprocessed_to_passive     true
% 3.00/1.02  --inst_prop_sim_given                   true
% 3.00/1.02  --inst_prop_sim_new                     false
% 3.00/1.02  --inst_subs_new                         false
% 3.00/1.02  --inst_eq_res_simp                      false
% 3.00/1.02  --inst_subs_given                       false
% 3.00/1.02  --inst_orphan_elimination               true
% 3.00/1.02  --inst_learning_loop_flag               true
% 3.00/1.02  --inst_learning_start                   3000
% 3.00/1.02  --inst_learning_factor                  2
% 3.00/1.02  --inst_start_prop_sim_after_learn       3
% 3.00/1.02  --inst_sel_renew                        solver
% 3.00/1.02  --inst_lit_activity_flag                true
% 3.00/1.02  --inst_restr_to_given                   false
% 3.00/1.02  --inst_activity_threshold               500
% 3.00/1.02  --inst_out_proof                        true
% 3.00/1.02  
% 3.00/1.02  ------ Resolution Options
% 3.00/1.02  
% 3.00/1.02  --resolution_flag                       false
% 3.00/1.02  --res_lit_sel                           adaptive
% 3.00/1.02  --res_lit_sel_side                      none
% 3.00/1.02  --res_ordering                          kbo
% 3.00/1.02  --res_to_prop_solver                    active
% 3.00/1.02  --res_prop_simpl_new                    false
% 3.00/1.02  --res_prop_simpl_given                  true
% 3.00/1.02  --res_passive_queue_type                priority_queues
% 3.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.02  --res_passive_queues_freq               [15;5]
% 3.00/1.02  --res_forward_subs                      full
% 3.00/1.02  --res_backward_subs                     full
% 3.00/1.02  --res_forward_subs_resolution           true
% 3.00/1.02  --res_backward_subs_resolution          true
% 3.00/1.02  --res_orphan_elimination                true
% 3.00/1.02  --res_time_limit                        2.
% 3.00/1.02  --res_out_proof                         true
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Options
% 3.00/1.02  
% 3.00/1.02  --superposition_flag                    true
% 3.00/1.02  --sup_passive_queue_type                priority_queues
% 3.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.02  --demod_completeness_check              fast
% 3.00/1.02  --demod_use_ground                      true
% 3.00/1.02  --sup_to_prop_solver                    passive
% 3.00/1.02  --sup_prop_simpl_new                    true
% 3.00/1.02  --sup_prop_simpl_given                  true
% 3.00/1.02  --sup_fun_splitting                     false
% 3.00/1.02  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ Proving...
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS status Theorem for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02   Resolution empty clause
% 3.00/1.02  
% 3.00/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  fof(f20,conjecture,(
% 3.00/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f21,negated_conjecture,(
% 3.00/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 3.00/1.02    inference(negated_conjecture,[],[f20])).
% 3.00/1.02  
% 3.00/1.02  fof(f51,plain,(
% 3.00/1.02    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f21])).
% 3.00/1.02  
% 3.00/1.02  fof(f52,plain,(
% 3.00/1.02    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f51])).
% 3.00/1.02  
% 3.00/1.02  fof(f69,plain,(
% 3.00/1.02    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.00/1.02    inference(nnf_transformation,[],[f52])).
% 3.00/1.02  
% 3.00/1.02  fof(f70,plain,(
% 3.00/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f69])).
% 3.00/1.02  
% 3.00/1.02  fof(f73,plain,(
% 3.00/1.02    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK6) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK6)) & (r1_waybel_7(X0,X1,sK6) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK6)) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f72,plain,(
% 3.00/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK5,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK5),X2)) & (r1_waybel_7(X0,sK5,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK5),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK5))) )),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f71,plain,(
% 3.00/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK4,X1,X2) | ~r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X1),X2)) & (r1_waybel_7(sK4,X1,X2) | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK4))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK4))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f74,plain,(
% 3.00/1.02    (((~r1_waybel_7(sK4,sK5,sK6) | ~r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6)) & (r1_waybel_7(sK4,sK5,sK6) | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4))) & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4))) & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) & ~v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f70,f73,f72,f71])).
% 3.00/1.02  
% 3.00/1.02  fof(f113,plain,(
% 3.00/1.02    v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f12,axiom,(
% 3.00/1.02    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f91,plain,(
% 3.00/1.02    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f12])).
% 3.00/1.02  
% 3.00/1.02  fof(f128,plain,(
% 3.00/1.02    v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))),
% 3.00/1.02    inference(definition_unfolding,[],[f113,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f15,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f24,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 3.00/1.02    inference(pure_predicate_removal,[],[f15])).
% 3.00/1.02  
% 3.00/1.02  fof(f41,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f24])).
% 3.00/1.02  
% 3.00/1.02  fof(f42,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f41])).
% 3.00/1.02  
% 3.00/1.02  fof(f99,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f42])).
% 3.00/1.02  
% 3.00/1.02  fof(f120,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f99,f91,f91,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f7,axiom,(
% 3.00/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f29,plain,(
% 3.00/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f7])).
% 3.00/1.02  
% 3.00/1.02  fof(f85,plain,(
% 3.00/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f29])).
% 3.00/1.02  
% 3.00/1.02  fof(f110,plain,(
% 3.00/1.02    l1_pre_topc(sK4)),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f108,plain,(
% 3.00/1.02    ~v2_struct_0(sK4)),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f114,plain,(
% 3.00/1.02    v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f127,plain,(
% 3.00/1.02    v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))),
% 3.00/1.02    inference(definition_unfolding,[],[f114,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f111,plain,(
% 3.00/1.02    ~v1_xboole_0(sK5)),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f6,axiom,(
% 3.00/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f28,plain,(
% 3.00/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f6])).
% 3.00/1.02  
% 3.00/1.02  fof(f84,plain,(
% 3.00/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f28])).
% 3.00/1.02  
% 3.00/1.02  fof(f115,plain,(
% 3.00/1.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f126,plain,(
% 3.00/1.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))),
% 3.00/1.02    inference(definition_unfolding,[],[f115,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f100,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f42])).
% 3.00/1.02  
% 3.00/1.02  fof(f119,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f100,f91,f91,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f118,plain,(
% 3.00/1.02    ~r1_waybel_7(sK4,sK5,sK6) | ~r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6)),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f18,axiom,(
% 3.00/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f47,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f18])).
% 3.00/1.02  
% 3.00/1.02  fof(f48,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f47])).
% 3.00/1.02  
% 3.00/1.02  fof(f68,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(nnf_transformation,[],[f48])).
% 3.00/1.02  
% 3.00/1.02  fof(f106,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f68])).
% 3.00/1.02  
% 3.00/1.02  fof(f109,plain,(
% 3.00/1.02    v2_pre_topc(sK4)),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f116,plain,(
% 3.00/1.02    m1_subset_1(sK6,u1_struct_0(sK4))),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f19,axiom,(
% 3.00/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f49,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f19])).
% 3.00/1.02  
% 3.00/1.02  fof(f50,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f49])).
% 3.00/1.02  
% 3.00/1.02  fof(f107,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f50])).
% 3.00/1.02  
% 3.00/1.02  fof(f125,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f107,f91,f91,f91,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f112,plain,(
% 3.00/1.02    v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f129,plain,(
% 3.00/1.02    v1_subset_1(sK5,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))),
% 3.00/1.02    inference(definition_unfolding,[],[f112,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f117,plain,(
% 3.00/1.02    r1_waybel_7(sK4,sK5,sK6) | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6)),
% 3.00/1.02    inference(cnf_transformation,[],[f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f105,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f68])).
% 3.00/1.02  
% 3.00/1.02  fof(f16,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f22,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 3.00/1.02    inference(pure_predicate_removal,[],[f16])).
% 3.00/1.02  
% 3.00/1.02  fof(f25,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 3.00/1.02    inference(pure_predicate_removal,[],[f22])).
% 3.00/1.02  
% 3.00/1.02  fof(f43,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f25])).
% 3.00/1.02  
% 3.00/1.02  fof(f44,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f43])).
% 3.00/1.02  
% 3.00/1.02  fof(f102,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f44])).
% 3.00/1.02  
% 3.00/1.02  fof(f121,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f102,f91,f91,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f17,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f23,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 3.00/1.02    inference(pure_predicate_removal,[],[f17])).
% 3.00/1.02  
% 3.00/1.02  fof(f45,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f23])).
% 3.00/1.02  
% 3.00/1.02  fof(f46,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f45])).
% 3.00/1.02  
% 3.00/1.02  fof(f104,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f46])).
% 3.00/1.02  
% 3.00/1.02  fof(f123,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f104,f91,f91,f91,f91])).
% 3.00/1.02  
% 3.00/1.02  fof(f5,axiom,(
% 3.00/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f83,plain,(
% 3.00/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f5])).
% 3.00/1.02  
% 3.00/1.02  fof(f4,axiom,(
% 3.00/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f82,plain,(
% 3.00/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.00/1.02    inference(cnf_transformation,[],[f4])).
% 3.00/1.02  
% 3.00/1.02  fof(f14,axiom,(
% 3.00/1.02    ! [X0] : (l1_struct_0(X0) => (v7_struct_0(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => X1 = X2))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f40,plain,(
% 3.00/1.02    ! [X0] : ((v7_struct_0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f14])).
% 3.00/1.02  
% 3.00/1.02  fof(f63,plain,(
% 3.00/1.02    ! [X0] : (((v7_struct_0(X0) | ? [X1] : (? [X2] : (X1 != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (X1 = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.00/1.02    inference(nnf_transformation,[],[f40])).
% 3.00/1.02  
% 3.00/1.02  fof(f64,plain,(
% 3.00/1.02    ! [X0] : (((v7_struct_0(X0) | ? [X1] : (? [X2] : (X1 != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.00/1.02    inference(rectify,[],[f63])).
% 3.00/1.02  
% 3.00/1.02  fof(f66,plain,(
% 3.00/1.02    ( ! [X1] : (! [X0] : (? [X2] : (X1 != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK3(X0) != X1 & m1_subset_1(sK3(X0),u1_struct_0(X0))))) )),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f65,plain,(
% 3.00/1.02    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK2(X0) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f67,plain,(
% 3.00/1.02    ! [X0] : (((v7_struct_0(X0) | ((sK2(X0) != sK3(X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f64,f66,f65])).
% 3.00/1.02  
% 3.00/1.02  fof(f97,plain,(
% 3.00/1.02    ( ! [X0] : (v7_struct_0(X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f67])).
% 3.00/1.02  
% 3.00/1.02  fof(f3,axiom,(
% 3.00/1.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f27,plain,(
% 3.00/1.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f3])).
% 3.00/1.02  
% 3.00/1.02  fof(f57,plain,(
% 3.00/1.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.00/1.02    inference(nnf_transformation,[],[f27])).
% 3.00/1.02  
% 3.00/1.02  fof(f80,plain,(
% 3.00/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f57])).
% 3.00/1.02  
% 3.00/1.02  fof(f98,plain,(
% 3.00/1.02    ( ! [X0] : (v7_struct_0(X0) | sK2(X0) != sK3(X0) | ~l1_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f67])).
% 3.00/1.02  
% 3.00/1.02  fof(f2,axiom,(
% 3.00/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f26,plain,(
% 3.00/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f2])).
% 3.00/1.02  
% 3.00/1.02  fof(f77,plain,(
% 3.00/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f26])).
% 3.00/1.02  
% 3.00/1.02  fof(f96,plain,(
% 3.00/1.02    ( ! [X0] : (v7_struct_0(X0) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f67])).
% 3.00/1.02  
% 3.00/1.02  fof(f13,axiom,(
% 3.00/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f38,plain,(
% 3.00/1.02    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f13])).
% 3.00/1.02  
% 3.00/1.02  fof(f39,plain,(
% 3.00/1.02    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f38])).
% 3.00/1.02  
% 3.00/1.02  fof(f59,plain,(
% 3.00/1.02    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(nnf_transformation,[],[f39])).
% 3.00/1.02  
% 3.00/1.02  fof(f60,plain,(
% 3.00/1.02    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(rectify,[],[f59])).
% 3.00/1.02  
% 3.00/1.02  fof(f61,plain,(
% 3.00/1.02    ! [X0] : (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f62,plain,(
% 3.00/1.02    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).
% 3.00/1.02  
% 3.00/1.02  fof(f92,plain,(
% 3.00/1.02    ( ! [X0] : (m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f62])).
% 3.00/1.02  
% 3.00/1.02  fof(f95,plain,(
% 3.00/1.02    ( ! [X4,X0,X3] : (X3 = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f67])).
% 3.00/1.02  
% 3.00/1.02  fof(f93,plain,(
% 3.00/1.02    ( ! [X0] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK1(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f62])).
% 3.00/1.02  
% 3.00/1.02  fof(f1,axiom,(
% 3.00/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f53,plain,(
% 3.00/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.02    inference(nnf_transformation,[],[f1])).
% 3.00/1.02  
% 3.00/1.02  fof(f54,plain,(
% 3.00/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.02    inference(rectify,[],[f53])).
% 3.00/1.02  
% 3.00/1.02  fof(f55,plain,(
% 3.00/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f56,plain,(
% 3.00/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).
% 3.00/1.02  
% 3.00/1.02  fof(f75,plain,(
% 3.00/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f56])).
% 3.00/1.02  
% 3.00/1.02  fof(f11,axiom,(
% 3.00/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f36,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f11])).
% 3.00/1.02  
% 3.00/1.02  fof(f37,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f36])).
% 3.00/1.02  
% 3.00/1.02  fof(f90,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f8,axiom,(
% 3.00/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f30,plain,(
% 3.00/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f8])).
% 3.00/1.02  
% 3.00/1.02  fof(f31,plain,(
% 3.00/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f30])).
% 3.00/1.02  
% 3.00/1.02  fof(f86,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f31])).
% 3.00/1.02  
% 3.00/1.02  fof(f9,axiom,(
% 3.00/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f32,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f9])).
% 3.00/1.02  
% 3.00/1.02  fof(f33,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f32])).
% 3.00/1.02  
% 3.00/1.02  fof(f58,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(nnf_transformation,[],[f33])).
% 3.00/1.02  
% 3.00/1.02  fof(f87,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f58])).
% 3.00/1.02  
% 3.00/1.02  fof(f10,axiom,(
% 3.00/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f34,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f10])).
% 3.00/1.02  
% 3.00/1.02  fof(f35,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.00/1.02    inference(flattening,[],[f34])).
% 3.00/1.02  
% 3.00/1.02  fof(f89,plain,(
% 3.00/1.02    ( ! [X0,X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f35])).
% 3.00/1.02  
% 3.00/1.02  cnf(c_37,negated_conjecture,
% 3.00/1.02      ( v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f128]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_24,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | v2_struct_0(X2)
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 3.00/1.02      | ~ l1_struct_0(X2)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f120]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_10,plain,
% 3.00/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_40,negated_conjecture,
% 3.00/1.02      ( l1_pre_topc(sK4) ),
% 3.00/1.02      inference(cnf_transformation,[],[f110]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1008,plain,
% 3.00/1.02      ( l1_struct_0(X0) | sK4 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_40]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1009,plain,
% 3.00/1.02      ( l1_struct_0(sK4) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1008]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1977,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | v2_struct_0(X2)
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | sK4 != X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_1009]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1978,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | v2_struct_0(sK4)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1977]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_42,negated_conjecture,
% 3.00/1.02      ( ~ v2_struct_0(sK4) ),
% 3.00/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1982,plain,
% 3.00/1.02      ( ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1978,c_42]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1983,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_1982]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_36,negated_conjecture,
% 3.00/1.02      ( v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f127]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2483,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
% 3.00/1.02      | sK5 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_1983,c_36]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2484,plain,
% 3.00/1.02      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_2483]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_39,negated_conjecture,
% 3.00/1.02      ( ~ v1_xboole_0(sK5) ),
% 3.00/1.02      inference(cnf_transformation,[],[f111]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2488,plain,
% 3.00/1.02      ( v1_xboole_0(X0)
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2484,c_39]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2489,plain,
% 3.00/1.02      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_2488]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3036,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | sK5 != sK5 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_37,c_2489]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3488,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v2_struct_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_3036]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4710,plain,
% 3.00/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.00/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,X0,sK5)) != iProver_top
% 3.00/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_3488]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_9,plain,
% 3.00/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1867,plain,
% 3.00/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_1009]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1868,plain,
% 3.00/1.02      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1867]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4836,plain,
% 3.00/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,X0,sK5)) != iProver_top
% 3.00/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_4710,c_1868]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5497,plain,
% 3.00/1.02      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
% 3.00/1.02      inference(equality_resolution,[status(thm)],[c_4836]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_35,negated_conjecture,
% 3.00/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f126]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_50,plain,
% 3.00/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_23,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | v2_struct_0(X2)
% 3.00/1.02      | ~ l1_struct_0(X2)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f119]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_32,negated_conjecture,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
% 3.00/1.02      inference(cnf_transformation,[],[f118]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_339,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
% 3.00/1.02      inference(prop_impl,[status(thm)],[c_32]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_29,plain,
% 3.00/1.02      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 3.00/1.02      | r3_waybel_9(X0,X1,X2)
% 3.00/1.02      | ~ l1_waybel_0(X1,X0)
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ v7_waybel_0(X1)
% 3.00/1.02      | ~ v4_orders_2(X1)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | v2_struct_0(X1)
% 3.00/1.02      | ~ v2_pre_topc(X0)
% 3.00/1.02      | ~ l1_pre_topc(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f106]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_41,negated_conjecture,
% 3.00/1.02      ( v2_pre_topc(sK4) ),
% 3.00/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_930,plain,
% 3.00/1.02      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 3.00/1.02      | r3_waybel_9(X0,X1,X2)
% 3.00/1.02      | ~ l1_waybel_0(X1,X0)
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ v7_waybel_0(X1)
% 3.00/1.02      | ~ v4_orders_2(X1)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | v2_struct_0(X1)
% 3.00/1.02      | ~ l1_pre_topc(X0)
% 3.00/1.02      | sK4 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_931,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
% 3.00/1.02      | r3_waybel_9(sK4,X0,X1)
% 3.00/1.02      | ~ l1_waybel_0(X0,sK4)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(X0)
% 3.00/1.02      | ~ v4_orders_2(X0)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | v2_struct_0(sK4)
% 3.00/1.02      | ~ l1_pre_topc(sK4) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_930]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_935,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
% 3.00/1.02      | r3_waybel_9(sK4,X0,X1)
% 3.00/1.02      | ~ l1_waybel_0(X0,sK4)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(X0)
% 3.00/1.02      | ~ v4_orders_2(X0)
% 3.00/1.02      | v2_struct_0(X0) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_931,c_42,c_40]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1400,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ l1_waybel_0(X0,sK4)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(X0)
% 3.00/1.02      | ~ v4_orders_2(X0)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != X0
% 3.00/1.02      | sK6 != X1
% 3.00/1.02      | sK4 != sK4 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_339,c_935]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1401,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
% 3.00/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1400]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_34,negated_conjecture,
% 3.00/1.02      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f116]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1403,plain,
% 3.00/1.02      ( ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1401,c_34]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1404,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_1403]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1440,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(X2)
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ l1_struct_0(X2)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(X2,X1,X0)
% 3.00/1.02      | sK4 != X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_1404]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1441,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(sK4)
% 3.00/1.02      | ~ l1_struct_0(sK4)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1440]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_116,plain,
% 3.00/1.02      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1445,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_1441,c_42,c_40,c_116]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2588,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
% 3.00/1.02      | sK5 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_1445,c_36]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2589,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(sK5)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_2588]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2593,plain,
% 3.00/1.02      ( v1_xboole_0(X0)
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2589,c_39]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2594,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_2593]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2937,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | sK5 != sK5 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_37,c_2594]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3500,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_2937]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4199,plain,
% 3.00/1.02      ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | sP0_iProver_split ),
% 3.00/1.02      inference(splitting,
% 3.00/1.02                [splitting(split),new_symbols(definition,[])],
% 3.00/1.02                [c_3500]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4705,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6) != iProver_top
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6) != iProver_top
% 3.00/1.02      | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
% 3.00/1.02      | sP0_iProver_split = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_4199]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_31,plain,
% 3.00/1.02      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 3.00/1.02      | v2_struct_0(X1)
% 3.00/1.02      | ~ l1_struct_0(X1)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f125]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_38,negated_conjecture,
% 3.00/1.02      ( v1_subset_1(sK5,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f129]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_611,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 3.00/1.02      | v2_struct_0(X1)
% 3.00/1.02      | ~ l1_struct_0(X1)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 3.00/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 3.00/1.02      | sK5 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_31,c_38]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_612,plain,
% 3.00/1.02      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | ~ l1_struct_0(X0)
% 3.00/1.02      | v1_xboole_0(sK5)
% 3.00/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
% 3.00/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_611]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_616,plain,
% 3.00/1.02      ( ~ l1_struct_0(X0)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 3.00/1.02      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
% 3.00/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_612,c_39]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_617,plain,
% 3.00/1.02      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | ~ l1_struct_0(X0)
% 3.00/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
% 3.00/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_616]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1798,plain,
% 3.00/1.02      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK5)) = sK5
% 3.00/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 3.00/1.02      | sK4 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_617,c_1009]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1799,plain,
% 3.00/1.02      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 3.00/1.02      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
% 3.00/1.02      | v2_struct_0(sK4)
% 3.00/1.02      | k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = sK5
% 3.00/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1798]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1801,plain,
% 3.00/1.02      ( k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = sK5
% 3.00/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_1799,c_42,c_37,c_36,c_35]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3515,plain,
% 3.00/1.02      ( k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = sK5 ),
% 3.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_1801]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4885,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,sK5,sK6) != iProver_top
% 3.00/1.02      | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
% 3.00/1.02      | sP0_iProver_split = iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_4705,c_3515]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_33,negated_conjecture,
% 3.00/1.02      ( r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
% 3.00/1.02      inference(cnf_transformation,[],[f117]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_341,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK6) ),
% 3.00/1.02      inference(prop_impl,[status(thm)],[c_33]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_30,plain,
% 3.00/1.02      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 3.00/1.02      | ~ r3_waybel_9(X0,X1,X2)
% 3.00/1.02      | ~ l1_waybel_0(X1,X0)
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ v7_waybel_0(X1)
% 3.00/1.02      | ~ v4_orders_2(X1)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | v2_struct_0(X1)
% 3.00/1.02      | ~ v2_pre_topc(X0)
% 3.00/1.02      | ~ l1_pre_topc(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f105]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_897,plain,
% 3.00/1.02      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 3.00/1.02      | ~ r3_waybel_9(X0,X1,X2)
% 3.00/1.02      | ~ l1_waybel_0(X1,X0)
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ v7_waybel_0(X1)
% 3.00/1.02      | ~ v4_orders_2(X1)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | v2_struct_0(X1)
% 3.00/1.02      | ~ l1_pre_topc(X0)
% 3.00/1.02      | sK4 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_898,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
% 3.00/1.02      | ~ r3_waybel_9(sK4,X0,X1)
% 3.00/1.02      | ~ l1_waybel_0(X0,sK4)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(X0)
% 3.00/1.02      | ~ v4_orders_2(X0)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | v2_struct_0(sK4)
% 3.00/1.02      | ~ l1_pre_topc(sK4) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_897]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_902,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
% 3.00/1.02      | ~ r3_waybel_9(sK4,X0,X1)
% 3.00/1.02      | ~ l1_waybel_0(X0,sK4)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(X0)
% 3.00/1.02      | ~ v4_orders_2(X0)
% 3.00/1.02      | v2_struct_0(X0) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_898,c_42,c_40]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1374,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ l1_waybel_0(X0,sK4)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(X0)
% 3.00/1.02      | ~ v4_orders_2(X0)
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != X0
% 3.00/1.02      | sK6 != X1
% 3.00/1.02      | sK4 != sK4 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_341,c_902]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1375,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
% 3.00/1.02      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1374]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1377,plain,
% 3.00/1.02      ( ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1375,c_34]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1378,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_1377]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1488,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(X2)
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ l1_struct_0(X2)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(X2,X1,X0)
% 3.00/1.02      | sK4 != X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_1378]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1489,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(sK4)
% 3.00/1.02      | ~ l1_struct_0(sK4)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1488]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1493,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_1489,c_42,c_40,c_116]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2543,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X1,X0)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
% 3.00/1.02      | sK5 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_1493,c_36]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2544,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(sK5)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_2543]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2548,plain,
% 3.00/1.02      ( v1_xboole_0(X0)
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2544,c_39]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2549,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_2548]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2975,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | sK5 != sK5 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_37,c_2549]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3496,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_2975]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4200,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6)
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6)
% 3.00/1.02      | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
% 3.00/1.02      | sP0_iProver_split ),
% 3.00/1.02      inference(splitting,
% 3.00/1.02                [splitting(split),new_symbols(definition,[])],
% 3.00/1.02                [c_3496]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4707,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,k2_yellow19(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),sK6) = iProver_top
% 3.00/1.02      | r1_waybel_7(sK4,sK5,sK6) = iProver_top
% 3.00/1.02      | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
% 3.00/1.02      | sP0_iProver_split = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_4200]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4861,plain,
% 3.00/1.02      ( r1_waybel_7(sK4,sK5,sK6) = iProver_top
% 3.00/1.02      | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
% 3.00/1.02      | sP0_iProver_split = iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_4707,c_3515]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4891,plain,
% 3.00/1.02      ( v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) != iProver_top
% 3.00/1.02      | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
% 3.00/1.02      | sP0_iProver_split = iProver_top ),
% 3.00/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4885,c_4861]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4204,plain,( X0 = X0 ),theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5318,plain,
% 3.00/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) = k3_lattice3(k1_lattice3(k2_struct_0(sK4))) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_4204]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4198,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | ~ sP0_iProver_split ),
% 3.00/1.02      inference(splitting,
% 3.00/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.00/1.02                [c_3500]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4706,plain,
% 3.00/1.02      ( k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.00/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.02      | v1_xboole_0(X0) = iProver_top
% 3.00/1.02      | sP0_iProver_split != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_4198]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4847,plain,
% 3.00/1.02      ( k3_yellow19(sK4,k2_struct_0(sK4),sK5) != k3_yellow19(sK4,X0,sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.02      | v1_xboole_0(X0) = iProver_top
% 3.00/1.02      | sP0_iProver_split != iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_4706,c_1868]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5730,plain,
% 3.00/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(k2_struct_0(sK4)))
% 3.00/1.02      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
% 3.00/1.02      | v1_xboole_0(k2_struct_0(sK4)) = iProver_top
% 3.00/1.02      | sP0_iProver_split != iProver_top ),
% 3.00/1.02      inference(equality_resolution,[status(thm)],[c_4847]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_25,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 3.00/1.02      | v2_struct_0(X2)
% 3.00/1.02      | ~ l1_struct_0(X2)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f121]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1944,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 3.00/1.02      | v2_struct_0(X2)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | sK4 != X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_25,c_1009]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1945,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | v2_struct_0(sK4)
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_1944]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1949,plain,
% 3.00/1.02      ( v4_orders_2(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1945,c_42]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1950,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_1949]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2513,plain,
% 3.00/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,X1,X0))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(X1)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X1))
% 3.00/1.02      | sK5 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_1950,c_36]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2514,plain,
% 3.00/1.02      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,X0,sK5))
% 3.00/1.02      | v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(sK5)
% 3.00/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_2513]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2518,plain,
% 3.00/1.02      ( v1_xboole_0(X0)
% 3.00/1.02      | v4_orders_2(k3_yellow19(sK4,X0,sK5))
% 3.00/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.02      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.03      inference(global_propositional_subsumption,[status(thm)],[c_2514,c_39]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_2519,plain,
% 3.00/1.03      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v4_orders_2(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.03      inference(renaming,[status(thm)],[c_2518]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_3013,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v4_orders_2(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | sK5 != sK5 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_37,c_2519]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_3492,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v4_orders_2(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0)) ),
% 3.00/1.03      inference(equality_resolution_simp,[status(thm)],[c_3013]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4709,plain,
% 3.00/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.00/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.03      | v4_orders_2(k3_yellow19(sK4,X0,sK5)) = iProver_top
% 3.00/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_3492]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4825,plain,
% 3.00/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.03      | v4_orders_2(k3_yellow19(sK4,X0,sK5)) = iProver_top
% 3.00/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4709,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5828,plain,
% 3.00/1.03      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
% 3.00/1.03      | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
% 3.00/1.03      inference(equality_resolution,[status(thm)],[c_4825]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_27,plain,
% 3.00/1.03      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 3.00/1.03      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.03      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 3.00/1.03      | v2_struct_0(X2)
% 3.00/1.03      | ~ l1_struct_0(X2)
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | v1_xboole_0(X1) ),
% 3.00/1.03      inference(cnf_transformation,[],[f123]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_572,plain,
% 3.00/1.03      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.03      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.00/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 3.00/1.03      | v2_struct_0(X2)
% 3.00/1.03      | ~ l1_struct_0(X2)
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | v1_xboole_0(X1)
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 3.00/1.03      | sK5 != X0 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_573,plain,
% 3.00/1.03      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(X1,X0,sK5))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ l1_struct_0(X1)
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | v1_xboole_0(sK5)
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_572]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_577,plain,
% 3.00/1.03      ( v1_xboole_0(X0)
% 3.00/1.03      | ~ l1_struct_0(X1)
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | v7_waybel_0(k3_yellow19(X1,X0,sK5))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.00/1.03      inference(global_propositional_subsumption,[status(thm)],[c_573,c_39]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_578,plain,
% 3.00/1.03      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(X1,X0,sK5))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ l1_struct_0(X1)
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.00/1.03      inference(renaming,[status(thm)],[c_577]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1872,plain,
% 3.00/1.03      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(X1,X0,sK5))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | sK4 != X1 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_578,c_1009]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1873,plain,
% 3.00/1.03      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v2_struct_0(sK4)
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_1872]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1877,plain,
% 3.00/1.03      ( v7_waybel_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.00/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1873,c_42]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1878,plain,
% 3.00/1.03      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ v13_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.00/1.03      inference(renaming,[status(thm)],[c_1877]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_2633,plain,
% 3.00/1.03      ( ~ v2_waybel_0(sK5,k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | sK5 != sK5 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_36,c_1878]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_2911,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | sK5 != sK5 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_37,c_2633]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_3504,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,X0,sK5))
% 3.00/1.03      | v1_xboole_0(X0)
% 3.00/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.00/1.03      inference(equality_resolution_simp,[status(thm)],[c_2911]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4704,plain,
% 3.00/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.00/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,X0,sK5)) = iProver_top
% 3.00/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_3504]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4872,plain,
% 3.00/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(X0))
% 3.00/1.03      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.00/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,X0,sK5)) = iProver_top
% 3.00/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4704,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5887,plain,
% 3.00/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK4))) != k3_lattice3(k1_lattice3(k2_struct_0(sK4)))
% 3.00/1.03      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) != iProver_top
% 3.00/1.03      | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) = iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
% 3.00/1.03      inference(equality_resolution,[status(thm)],[c_4872]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6259,plain,
% 3.00/1.03      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
% 3.00/1.03      inference(global_propositional_subsumption,
% 3.00/1.03                [status(thm)],
% 3.00/1.03                [c_5497,c_50,c_4891,c_5318,c_5730,c_5828,c_5887]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_8,plain,
% 3.00/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.00/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4726,plain,
% 3.00/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7,plain,
% 3.00/1.03      ( k2_subset_1(X0) = X0 ),
% 3.00/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4741,plain,
% 3.00/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4726,c_7]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6265,plain,
% 3.00/1.03      ( v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
% 3.00/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_6259,c_4741]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_20,plain,
% 3.00/1.03      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
% 3.00/1.03      | v7_struct_0(X0)
% 3.00/1.03      | ~ l1_struct_0(X0) ),
% 3.00/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1819,plain,
% 3.00/1.03      ( m1_subset_1(sK3(X0),u1_struct_0(X0)) | v7_struct_0(X0) | sK4 != X0 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_1009]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1820,plain,
% 3.00/1.03      ( m1_subset_1(sK3(sK4),u1_struct_0(sK4)) | v7_struct_0(sK4) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_1819]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4716,plain,
% 3.00/1.03      ( m1_subset_1(sK3(sK4),u1_struct_0(sK4)) = iProver_top
% 3.00/1.03      | v7_struct_0(sK4) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4756,plain,
% 3.00/1.03      ( m1_subset_1(sK3(sK4),k2_struct_0(sK4)) = iProver_top
% 3.00/1.03      | v7_struct_0(sK4) = iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4716,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.00/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4727,plain,
% 3.00/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 3.00/1.03      | v1_xboole_0(X1) != iProver_top
% 3.00/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5735,plain,
% 3.00/1.03      ( v7_struct_0(sK4) = iProver_top
% 3.00/1.03      | v1_xboole_0(sK3(sK4)) = iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_4756,c_4727]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_45,plain,
% 3.00/1.03      ( l1_pre_topc(sK4) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_19,plain,
% 3.00/1.03      ( v7_struct_0(X0) | ~ l1_struct_0(X0) | sK3(X0) != sK2(X0) ),
% 3.00/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_88,plain,
% 3.00/1.03      ( sK3(X0) != sK2(X0)
% 3.00/1.03      | v7_struct_0(X0) = iProver_top
% 3.00/1.03      | l1_struct_0(X0) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_90,plain,
% 3.00/1.03      ( sK3(sK4) != sK2(sK4)
% 3.00/1.03      | v7_struct_0(sK4) = iProver_top
% 3.00/1.03      | l1_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(instantiation,[status(thm)],[c_88]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_115,plain,
% 3.00/1.03      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_117,plain,
% 3.00/1.03      ( l1_pre_topc(sK4) != iProver_top | l1_struct_0(sK4) = iProver_top ),
% 3.00/1.03      inference(instantiation,[status(thm)],[c_115]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_2,plain,
% 3.00/1.03      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.00/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5667,plain,
% 3.00/1.03      ( ~ v1_xboole_0(sK3(sK4))
% 3.00/1.03      | ~ v1_xboole_0(sK2(sK4))
% 3.00/1.03      | sK3(sK4) = sK2(sK4) ),
% 3.00/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5671,plain,
% 3.00/1.03      ( sK3(sK4) = sK2(sK4)
% 3.00/1.03      | v1_xboole_0(sK3(sK4)) != iProver_top
% 3.00/1.03      | v1_xboole_0(sK2(sK4)) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_5667]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_21,plain,
% 3.00/1.03      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
% 3.00/1.03      | v7_struct_0(X0)
% 3.00/1.03      | ~ l1_struct_0(X0) ),
% 3.00/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1809,plain,
% 3.00/1.03      ( m1_subset_1(sK2(X0),u1_struct_0(X0)) | v7_struct_0(X0) | sK4 != X0 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_1009]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1810,plain,
% 3.00/1.03      ( m1_subset_1(sK2(sK4),u1_struct_0(sK4)) | v7_struct_0(sK4) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_1809]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4717,plain,
% 3.00/1.03      ( m1_subset_1(sK2(sK4),u1_struct_0(sK4)) = iProver_top
% 3.00/1.03      | v7_struct_0(sK4) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4761,plain,
% 3.00/1.03      ( m1_subset_1(sK2(sK4),k2_struct_0(sK4)) = iProver_top
% 3.00/1.03      | v7_struct_0(sK4) = iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4717,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5812,plain,
% 3.00/1.03      ( v7_struct_0(sK4) = iProver_top
% 3.00/1.03      | v1_xboole_0(sK2(sK4)) = iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_4761,c_4727]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6096,plain,
% 3.00/1.03      ( v7_struct_0(sK4) = iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
% 3.00/1.03      inference(global_propositional_subsumption,
% 3.00/1.03                [status(thm)],
% 3.00/1.03                [c_5735,c_45,c_90,c_117,c_5671,c_5812]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6269,plain,
% 3.00/1.03      ( v7_struct_0(sK4) = iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_6265,c_6096]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_18,plain,
% 3.00/1.03      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
% 3.00/1.03      | ~ v7_struct_0(X0)
% 3.00/1.03      | v2_struct_0(X0)
% 3.00/1.03      | ~ l1_struct_0(X0) ),
% 3.00/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1839,plain,
% 3.00/1.03      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
% 3.00/1.03      | ~ v7_struct_0(X0)
% 3.00/1.03      | v2_struct_0(X0)
% 3.00/1.03      | sK4 != X0 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_1009]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1840,plain,
% 3.00/1.03      ( m1_subset_1(sK1(sK4),u1_struct_0(sK4))
% 3.00/1.03      | ~ v7_struct_0(sK4)
% 3.00/1.03      | v2_struct_0(sK4) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_1839]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1842,plain,
% 3.00/1.03      ( ~ v7_struct_0(sK4) | m1_subset_1(sK1(sK4),u1_struct_0(sK4)) ),
% 3.00/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1840,c_42]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1843,plain,
% 3.00/1.03      ( m1_subset_1(sK1(sK4),u1_struct_0(sK4)) | ~ v7_struct_0(sK4) ),
% 3.00/1.03      inference(renaming,[status(thm)],[c_1842]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4714,plain,
% 3.00/1.03      ( m1_subset_1(sK1(sK4),u1_struct_0(sK4)) = iProver_top
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_1843]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4766,plain,
% 3.00/1.03      ( m1_subset_1(sK1(sK4),k2_struct_0(sK4)) = iProver_top
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4714,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4725,plain,
% 3.00/1.03      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4738,plain,
% 3.00/1.03      ( m1_subset_1(sK6,k2_struct_0(sK4)) = iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4725,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_22,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | ~ v7_struct_0(X1)
% 3.00/1.03      | ~ l1_struct_0(X1)
% 3.00/1.03      | X0 = X2 ),
% 3.00/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1905,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | ~ v7_struct_0(X1)
% 3.00/1.03      | X0 = X2
% 3.00/1.03      | sK4 != X1 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_1009]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1906,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.00/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.00/1.03      | ~ v7_struct_0(sK4)
% 3.00/1.03      | X1 = X0 ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_1905]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4712,plain,
% 3.00/1.03      ( X0 = X1
% 3.00/1.03      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.00/1.03      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_1906]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4815,plain,
% 3.00/1.03      ( X0 = X1
% 3.00/1.03      | m1_subset_1(X1,k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4712,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5379,plain,
% 3.00/1.03      ( sK6 = X0
% 3.00/1.03      | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_4738,c_4815]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5416,plain,
% 3.00/1.03      ( sK1(sK4) = sK6 | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_4766,c_5379]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6527,plain,
% 3.00/1.03      ( sK1(sK4) = sK6 ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_6269,c_5416]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_5174,plain,
% 3.00/1.03      ( v1_xboole_0(k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | v1_xboole_0(sK6) = iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_4738,c_4727]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6273,plain,
% 3.00/1.03      ( v1_xboole_0(sK6) = iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_6265,c_5174]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4729,plain,
% 3.00/1.03      ( X0 = X1
% 3.00/1.03      | v1_xboole_0(X0) != iProver_top
% 3.00/1.03      | v1_xboole_0(X1) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6267,plain,
% 3.00/1.03      ( k2_struct_0(sK4) = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_6265,c_4729]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6382,plain,
% 3.00/1.03      ( k2_struct_0(sK4) = sK6 ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_6273,c_6267]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_17,plain,
% 3.00/1.03      ( ~ v7_struct_0(X0)
% 3.00/1.03      | v2_struct_0(X0)
% 3.00/1.03      | ~ l1_struct_0(X0)
% 3.00/1.03      | k6_domain_1(u1_struct_0(X0),sK1(X0)) = u1_struct_0(X0) ),
% 3.00/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1853,plain,
% 3.00/1.03      ( ~ v7_struct_0(X0)
% 3.00/1.03      | v2_struct_0(X0)
% 3.00/1.03      | k6_domain_1(u1_struct_0(X0),sK1(X0)) = u1_struct_0(X0)
% 3.00/1.03      | sK4 != X0 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_1009]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1854,plain,
% 3.00/1.03      ( ~ v7_struct_0(sK4)
% 3.00/1.03      | v2_struct_0(sK4)
% 3.00/1.03      | k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_1853]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_95,plain,
% 3.00/1.03      ( ~ v7_struct_0(sK4)
% 3.00/1.03      | v2_struct_0(sK4)
% 3.00/1.03      | ~ l1_struct_0(sK4)
% 3.00/1.03      | k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4) ),
% 3.00/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1856,plain,
% 3.00/1.03      ( ~ v7_struct_0(sK4)
% 3.00/1.03      | k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4) ),
% 3.00/1.03      inference(global_propositional_subsumption,
% 3.00/1.03                [status(thm)],
% 3.00/1.03                [c_1854,c_42,c_40,c_95,c_116]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4713,plain,
% 3.00/1.03      ( k6_domain_1(u1_struct_0(sK4),sK1(sK4)) = u1_struct_0(sK4)
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_1856]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4771,plain,
% 3.00/1.03      ( k6_domain_1(k2_struct_0(sK4),sK1(sK4)) = k2_struct_0(sK4)
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4713,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6554,plain,
% 3.00/1.03      ( k6_domain_1(sK6,sK1(sK4)) = sK6 | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(demodulation,[status(thm)],[c_6382,c_4771]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6948,plain,
% 3.00/1.03      ( k6_domain_1(sK6,sK1(sK4)) = sK6 ),
% 3.00/1.03      inference(global_propositional_subsumption,
% 3.00/1.03                [status(thm)],
% 3.00/1.03                [c_6554,c_6096,c_6265]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7612,plain,
% 3.00/1.03      ( k6_domain_1(sK6,sK6) = sK6 ),
% 3.00/1.03      inference(demodulation,[status(thm)],[c_6527,c_6948]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1,plain,
% 3.00/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.00/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_15,plain,
% 3.00/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | r2_hidden(X2,X0)
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X1) ),
% 3.00/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_11,plain,
% 3.00/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X1) ),
% 3.00/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_260,plain,
% 3.00/1.03      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_connsp_2(X0,X1,X2)
% 3.00/1.03      | r2_hidden(X2,X0)
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X1) ),
% 3.00/1.03      inference(global_propositional_subsumption,[status(thm)],[c_15,c_11]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_261,plain,
% 3.00/1.03      ( ~ m1_connsp_2(X0,X1,X2)
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | r2_hidden(X2,X0)
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X1) ),
% 3.00/1.03      inference(renaming,[status(thm)],[c_260]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_13,plain,
% 3.00/1.03      ( ~ m2_connsp_2(X0,X1,k6_domain_1(u1_struct_0(X1),X2))
% 3.00/1.03      | m1_connsp_2(X0,X1,X2)
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X1) ),
% 3.00/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_14,plain,
% 3.00/1.03      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
% 3.00/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/1.03      | v2_struct_0(X0)
% 3.00/1.03      | ~ v2_pre_topc(X0)
% 3.00/1.03      | ~ l1_pre_topc(X0) ),
% 3.00/1.03      inference(cnf_transformation,[],[f89]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_663,plain,
% 3.00/1.03      ( m1_connsp_2(X0,X1,X2)
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | v2_struct_0(X4)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ v2_pre_topc(X4)
% 3.00/1.03      | ~ l1_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X4)
% 3.00/1.03      | X4 != X1
% 3.00/1.03      | k6_domain_1(u1_struct_0(X1),X2) != X3
% 3.00/1.03      | k2_struct_0(X4) != X0 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_14]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_664,plain,
% 3.00/1.03      ( m1_connsp_2(k2_struct_0(X0),X0,X1)
% 3.00/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/1.03      | v2_struct_0(X0)
% 3.00/1.03      | ~ v2_pre_topc(X0)
% 3.00/1.03      | ~ l1_pre_topc(X0) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_663]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_776,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X3),X2),k1_zfmisc_1(u1_struct_0(X3)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 3.00/1.03      | r2_hidden(X0,X4)
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | v2_struct_0(X3)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ v2_pre_topc(X3)
% 3.00/1.03      | ~ l1_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X3)
% 3.00/1.03      | X3 != X1
% 3.00/1.03      | X2 != X0
% 3.00/1.03      | k2_struct_0(X3) != X4 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_261,c_664]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_777,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | r2_hidden(X0,k2_struct_0(X1))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ v2_pre_topc(X1)
% 3.00/1.03      | ~ l1_pre_topc(X1) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_776]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_963,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.03      | r2_hidden(X0,k2_struct_0(X1))
% 3.00/1.03      | v2_struct_0(X1)
% 3.00/1.03      | ~ l1_pre_topc(X1)
% 3.00/1.03      | sK4 != X1 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_777,c_41]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_964,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | r2_hidden(X0,k2_struct_0(sK4))
% 3.00/1.03      | v2_struct_0(sK4)
% 3.00/1.03      | ~ l1_pre_topc(sK4) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_963]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_968,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | r2_hidden(X0,k2_struct_0(sK4)) ),
% 3.00/1.03      inference(global_propositional_subsumption,
% 3.00/1.03                [status(thm)],
% 3.00/1.03                [c_964,c_42,c_40]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1049,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ v1_xboole_0(X1)
% 3.00/1.03      | X0 != X2
% 3.00/1.03      | k2_struct_0(sK4) != X1 ),
% 3.00/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_968]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_1050,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ v1_xboole_0(k2_struct_0(sK4)) ),
% 3.00/1.03      inference(unflattening,[status(thm)],[c_1049]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4201,plain,
% 3.00/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.00/1.03      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ sP1_iProver_split ),
% 3.00/1.03      inference(splitting,
% 3.00/1.03                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.00/1.03                [c_1050]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4719,plain,
% 3.00/1.03      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.00/1.03      | m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.00/1.03      | sP1_iProver_split != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_4201]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4808,plain,
% 3.00/1.03      ( m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | m1_subset_1(k6_domain_1(k2_struct_0(sK4),X0),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.03      | sP1_iProver_split != iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4719,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6552,plain,
% 3.00/1.03      ( m1_subset_1(X0,sK6) != iProver_top
% 3.00/1.03      | m1_subset_1(k6_domain_1(sK6,X0),k1_zfmisc_1(sK6)) != iProver_top
% 3.00/1.03      | sP1_iProver_split != iProver_top ),
% 3.00/1.03      inference(demodulation,[status(thm)],[c_6382,c_4808]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4202,plain,
% 3.00/1.03      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.00/1.03      | ~ v1_xboole_0(k2_struct_0(sK4))
% 3.00/1.03      | sP1_iProver_split ),
% 3.00/1.03      inference(splitting,
% 3.00/1.03                [splitting(split),new_symbols(definition,[])],
% 3.00/1.03                [c_1050]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4718,plain,
% 3.00/1.03      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | sP1_iProver_split = iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_4202]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4794,plain,
% 3.00/1.03      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.00/1.03      | v1_xboole_0(k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | sP1_iProver_split = iProver_top ),
% 3.00/1.03      inference(light_normalisation,[status(thm)],[c_4718,c_1868]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_4798,plain,
% 3.00/1.03      ( v1_xboole_0(k2_struct_0(sK4)) != iProver_top
% 3.00/1.03      | sP1_iProver_split = iProver_top ),
% 3.00/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4794,c_4741]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7059,plain,
% 3.00/1.03      ( m1_subset_1(k6_domain_1(sK6,X0),k1_zfmisc_1(sK6)) != iProver_top
% 3.00/1.03      | m1_subset_1(X0,sK6) != iProver_top ),
% 3.00/1.03      inference(global_propositional_subsumption,
% 3.00/1.03                [status(thm)],
% 3.00/1.03                [c_6552,c_4798,c_6265]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7060,plain,
% 3.00/1.03      ( m1_subset_1(X0,sK6) != iProver_top
% 3.00/1.03      | m1_subset_1(k6_domain_1(sK6,X0),k1_zfmisc_1(sK6)) != iProver_top ),
% 3.00/1.03      inference(renaming,[status(thm)],[c_7059]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7617,plain,
% 3.00/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(sK6)) != iProver_top
% 3.00/1.03      | m1_subset_1(sK6,sK6) != iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_7612,c_7060]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6557,plain,
% 3.00/1.03      ( m1_subset_1(sK1(sK4),sK6) = iProver_top
% 3.00/1.03      | v7_struct_0(sK4) != iProver_top ),
% 3.00/1.03      inference(demodulation,[status(thm)],[c_6382,c_4766]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7068,plain,
% 3.00/1.03      ( m1_subset_1(sK1(sK4),sK6) != iProver_top
% 3.00/1.03      | m1_subset_1(sK6,k1_zfmisc_1(sK6)) != iProver_top ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_6948,c_7060]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7792,plain,
% 3.00/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(sK6)) != iProver_top ),
% 3.00/1.03      inference(global_propositional_subsumption,
% 3.00/1.03                [status(thm)],
% 3.00/1.03                [c_7617,c_6096,c_6265,c_6557,c_7068]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7797,plain,
% 3.00/1.03      ( $false ),
% 3.00/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_7792,c_4741]) ).
% 3.00/1.03  
% 3.00/1.03  
% 3.00/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.03  
% 3.00/1.03  ------                               Statistics
% 3.00/1.03  
% 3.00/1.03  ------ General
% 3.00/1.03  
% 3.00/1.03  abstr_ref_over_cycles:                  0
% 3.00/1.03  abstr_ref_under_cycles:                 0
% 3.00/1.03  gc_basic_clause_elim:                   0
% 3.00/1.03  forced_gc_time:                         0
% 3.00/1.03  parsing_time:                           0.01
% 3.00/1.03  unif_index_cands_time:                  0.
% 3.00/1.03  unif_index_add_time:                    0.
% 3.00/1.03  orderings_time:                         0.
% 3.00/1.03  out_proof_time:                         0.041
% 3.00/1.03  total_time:                             0.246
% 3.00/1.03  num_of_symbols:                         67
% 3.00/1.03  num_of_terms:                           3069
% 3.00/1.03  
% 3.00/1.03  ------ Preprocessing
% 3.00/1.03  
% 3.00/1.03  num_of_splits:                          3
% 3.00/1.03  num_of_split_atoms:                     2
% 3.00/1.03  num_of_reused_defs:                     1
% 3.00/1.03  num_eq_ax_congr_red:                    18
% 3.00/1.03  num_of_sem_filtered_clauses:            1
% 3.00/1.03  num_of_subtypes:                        0
% 3.00/1.03  monotx_restored_types:                  0
% 3.00/1.03  sat_num_of_epr_types:                   0
% 3.00/1.03  sat_num_of_non_cyclic_types:            0
% 3.00/1.03  sat_guarded_non_collapsed_types:        0
% 3.00/1.03  num_pure_diseq_elim:                    0
% 3.00/1.03  simp_replaced_by:                       0
% 3.00/1.03  res_preprocessed:                       164
% 3.00/1.03  prep_upred:                             0
% 3.00/1.03  prep_unflattend:                        69
% 3.00/1.03  smt_new_axioms:                         0
% 3.00/1.03  pred_elim_cands:                        7
% 3.00/1.03  pred_elim:                              11
% 3.00/1.03  pred_elim_cl:                           15
% 3.00/1.03  pred_elim_cycles:                       30
% 3.00/1.03  merged_defs:                            2
% 3.00/1.03  merged_defs_ncl:                        0
% 3.00/1.03  bin_hyper_res:                          2
% 3.00/1.03  prep_cycles:                            4
% 3.00/1.03  pred_elim_time:                         0.076
% 3.00/1.03  splitting_time:                         0.
% 3.00/1.03  sem_filter_time:                        0.
% 3.00/1.03  monotx_time:                            0.
% 3.00/1.03  subtype_inf_time:                       0.
% 3.00/1.03  
% 3.00/1.03  ------ Problem properties
% 3.00/1.03  
% 3.00/1.03  clauses:                                29
% 3.00/1.03  conjectures:                            4
% 3.00/1.03  epr:                                    5
% 3.00/1.03  horn:                                   22
% 3.00/1.03  ground:                                 14
% 3.00/1.03  unary:                                  8
% 3.00/1.03  binary:                                 6
% 3.00/1.03  lits:                                   86
% 3.00/1.03  lits_eq:                                16
% 3.00/1.03  fd_pure:                                0
% 3.00/1.03  fd_pseudo:                              0
% 3.00/1.03  fd_cond:                                0
% 3.00/1.03  fd_pseudo_cond:                         2
% 3.00/1.03  ac_symbols:                             0
% 3.00/1.03  
% 3.00/1.03  ------ Propositional Solver
% 3.00/1.03  
% 3.00/1.03  prop_solver_calls:                      29
% 3.00/1.03  prop_fast_solver_calls:                 2347
% 3.00/1.03  smt_solver_calls:                       0
% 3.00/1.03  smt_fast_solver_calls:                  0
% 3.00/1.03  prop_num_of_clauses:                    1841
% 3.00/1.03  prop_preprocess_simplified:             6090
% 3.00/1.03  prop_fo_subsumed:                       70
% 3.00/1.03  prop_solver_time:                       0.
% 3.00/1.03  smt_solver_time:                        0.
% 3.00/1.03  smt_fast_solver_time:                   0.
% 3.00/1.03  prop_fast_solver_time:                  0.
% 3.00/1.03  prop_unsat_core_time:                   0.
% 3.00/1.03  
% 3.00/1.03  ------ QBF
% 3.00/1.03  
% 3.00/1.03  qbf_q_res:                              0
% 3.00/1.03  qbf_num_tautologies:                    0
% 3.00/1.03  qbf_prep_cycles:                        0
% 3.00/1.03  
% 3.00/1.03  ------ BMC1
% 3.00/1.03  
% 3.00/1.03  bmc1_current_bound:                     -1
% 3.00/1.03  bmc1_last_solved_bound:                 -1
% 3.00/1.03  bmc1_unsat_core_size:                   -1
% 3.00/1.03  bmc1_unsat_core_parents_size:           -1
% 3.00/1.03  bmc1_merge_next_fun:                    0
% 3.00/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.03  
% 3.00/1.03  ------ Instantiation
% 3.00/1.03  
% 3.00/1.03  inst_num_of_clauses:                    468
% 3.00/1.03  inst_num_in_passive:                    137
% 3.00/1.03  inst_num_in_active:                     274
% 3.00/1.03  inst_num_in_unprocessed:                57
% 3.00/1.03  inst_num_of_loops:                      340
% 3.00/1.03  inst_num_of_learning_restarts:          0
% 3.00/1.03  inst_num_moves_active_passive:          62
% 3.00/1.03  inst_lit_activity:                      0
% 3.00/1.03  inst_lit_activity_moves:                0
% 3.00/1.03  inst_num_tautologies:                   0
% 3.00/1.03  inst_num_prop_implied:                  0
% 3.00/1.03  inst_num_existing_simplified:           0
% 3.00/1.03  inst_num_eq_res_simplified:             0
% 3.00/1.03  inst_num_child_elim:                    0
% 3.00/1.03  inst_num_of_dismatching_blockings:      115
% 3.00/1.03  inst_num_of_non_proper_insts:           514
% 3.00/1.03  inst_num_of_duplicates:                 0
% 3.00/1.03  inst_inst_num_from_inst_to_res:         0
% 3.00/1.03  inst_dismatching_checking_time:         0.
% 3.00/1.03  
% 3.00/1.03  ------ Resolution
% 3.00/1.03  
% 3.00/1.03  res_num_of_clauses:                     0
% 3.00/1.03  res_num_in_passive:                     0
% 3.00/1.03  res_num_in_active:                      0
% 3.00/1.03  res_num_of_loops:                       168
% 3.00/1.03  res_forward_subset_subsumed:            80
% 3.00/1.03  res_backward_subset_subsumed:           0
% 3.00/1.03  res_forward_subsumed:                   0
% 3.00/1.03  res_backward_subsumed:                  0
% 3.00/1.03  res_forward_subsumption_resolution:     2
% 3.00/1.03  res_backward_subsumption_resolution:    0
% 3.00/1.03  res_clause_to_clause_subsumption:       449
% 3.00/1.03  res_orphan_elimination:                 0
% 3.00/1.03  res_tautology_del:                      44
% 3.00/1.03  res_num_eq_res_simplified:              6
% 3.00/1.03  res_num_sel_changes:                    0
% 3.00/1.03  res_moves_from_active_to_pass:          0
% 3.00/1.03  
% 3.00/1.03  ------ Superposition
% 3.00/1.03  
% 3.00/1.03  sup_time_total:                         0.
% 3.00/1.03  sup_time_generating:                    0.
% 3.00/1.03  sup_time_sim_full:                      0.
% 3.00/1.03  sup_time_sim_immed:                     0.
% 3.00/1.03  
% 3.00/1.03  sup_num_of_clauses:                     39
% 3.00/1.03  sup_num_in_active:                      34
% 3.00/1.03  sup_num_in_passive:                     5
% 3.00/1.03  sup_num_of_loops:                       67
% 3.00/1.03  sup_fw_superposition:                   44
% 3.00/1.03  sup_bw_superposition:                   25
% 3.00/1.03  sup_immediate_simplified:               23
% 3.00/1.03  sup_given_eliminated:                   1
% 3.00/1.03  comparisons_done:                       0
% 3.00/1.03  comparisons_avoided:                    0
% 3.00/1.03  
% 3.00/1.03  ------ Simplifications
% 3.00/1.03  
% 3.00/1.03  
% 3.00/1.03  sim_fw_subset_subsumed:                 19
% 3.00/1.03  sim_bw_subset_subsumed:                 6
% 3.00/1.03  sim_fw_subsumed:                        2
% 3.00/1.03  sim_bw_subsumed:                        1
% 3.00/1.03  sim_fw_subsumption_res:                 4
% 3.00/1.03  sim_bw_subsumption_res:                 1
% 3.00/1.03  sim_tautology_del:                      11
% 3.00/1.03  sim_eq_tautology_del:                   6
% 3.00/1.03  sim_eq_res_simp:                        2
% 3.00/1.03  sim_fw_demodulated:                     1
% 3.00/1.03  sim_bw_demodulated:                     30
% 3.00/1.03  sim_light_normalised:                   20
% 3.00/1.03  sim_joinable_taut:                      0
% 3.00/1.03  sim_joinable_simp:                      0
% 3.00/1.03  sim_ac_normalised:                      0
% 3.00/1.03  sim_smt_subsumption:                    0
% 3.00/1.03  
%------------------------------------------------------------------------------
