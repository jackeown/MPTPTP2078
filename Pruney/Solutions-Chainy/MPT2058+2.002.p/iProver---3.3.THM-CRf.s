%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:14 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  236 (1891 expanded)
%              Number of clauses        :  154 ( 401 expanded)
%              Number of leaves         :   17 ( 528 expanded)
%              Depth                    :   33
%              Number of atoms          : 1457 (16928 expanded)
%              Number of equality atoms :  250 ( 541 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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
     => ( ( ~ r1_waybel_7(X0,X1,sK3)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3) )
        & ( r1_waybel_7(X0,X1,sK3)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f68,plain,(
    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f68,f53])).

fof(f69,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f69,f53])).

fof(f10,axiom,(
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

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(cnf_transformation,[],[f30])).

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
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(definition_unfolding,[],[f67,f53])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
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
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
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

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(definition_unfolding,[],[f70,f53])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f37])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(cnf_transformation,[],[f26])).

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
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

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

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(cnf_transformation,[],[f34])).

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
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
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

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(cnf_transformation,[],[f30])).

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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

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
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(cnf_transformation,[],[f28])).

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
    inference(cnf_transformation,[],[f28])).

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
    ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
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
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_348,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_349,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_353,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_23])).

cnf(c_354,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_546,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_547,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_1362,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_354,c_547])).

cnf(c_1363,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1367,plain,
    ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_26])).

cnf(c_1368,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1367])).

cnf(c_1808,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1368])).

cnf(c_2086,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1808])).

cnf(c_2669,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2086])).

cnf(c_3444,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2669])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1284,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_547])).

cnf(c_1285,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1284])).

cnf(c_3535,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3444,c_1285])).

cnf(c_4114,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3535])).

cnf(c_4261,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4114])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_66,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_68,plain,
    ( v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(sK0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_7,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_16,negated_conjecture,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_191,plain,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
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

cnf(c_471,plain,
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

cnf(c_472,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_476,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_26,c_24])).

cnf(c_875,plain,
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
    inference(resolution_lifted,[status(thm)],[c_191,c_476])).

cnf(c_876,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_875])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_878,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_876,c_18])).

cnf(c_879,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_878])).

cnf(c_915,plain,
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
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_879])).

cnf(c_916,plain,
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
    | ~ l1_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_70,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_920,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_916,c_26,c_24,c_70])).

cnf(c_1763,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_920,c_20])).

cnf(c_1764,plain,
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
    inference(unflattening,[status(thm)],[c_1763])).

cnf(c_1768,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_23])).

cnf(c_1769,plain,
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
    inference(renaming,[status(thm)],[c_1768])).

cnf(c_2112,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_1769])).

cnf(c_2665,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2112])).

cnf(c_3130,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2665])).

cnf(c_3445,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
    | r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3130])).

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

cnf(c_387,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_388,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK2)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_392,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_23])).

cnf(c_393,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_1273,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_547])).

cnf(c_1274,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v2_struct_0(sK1)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_1273])).

cnf(c_1276,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1274,c_26,c_21,c_20,c_19])).

cnf(c_2673,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1276])).

cnf(c_3548,plain,
    ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3445,c_2673])).

cnf(c_17,negated_conjecture,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_193,plain,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
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

cnf(c_438,plain,
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

cnf(c_439,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_443,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_26,c_24])).

cnf(c_849,plain,
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
    inference(resolution_lifted,[status(thm)],[c_193,c_443])).

cnf(c_850,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_852,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_18])).

cnf(c_853,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_852])).

cnf(c_963,plain,
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
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_853])).

cnf(c_964,plain,
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
    | ~ l1_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_963])).

cnf(c_968,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_964,c_26,c_24,c_70])).

cnf(c_1718,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_968,c_20])).

cnf(c_1719,plain,
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
    inference(unflattening,[status(thm)],[c_1718])).

cnf(c_1723,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1719,c_23])).

cnf(c_1724,plain,
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
    inference(renaming,[status(thm)],[c_1723])).

cnf(c_2150,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_1724])).

cnf(c_2661,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2150])).

cnf(c_3131,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2661])).

cnf(c_3447,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
    | r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3131])).

cnf(c_3524,plain,
    ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3447,c_2673])).

cnf(c_3554,plain,
    ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3548,c_3524])).

cnf(c_6,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_504,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_505,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_64,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_507,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_26,c_25,c_24,c_64])).

cnf(c_3452,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_3475,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3452,c_1285])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3457,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3769,plain,
    ( v1_xboole_0(sK0(sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3475,c_3457])).

cnf(c_12,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_147,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_10])).

cnf(c_148,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_1289,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_148,c_547])).

cnf(c_1290,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1289])).

cnf(c_1294,plain,
    ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1290,c_26])).

cnf(c_1295,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1294])).

cnf(c_1688,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1295,c_20])).

cnf(c_1689,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1688])).

cnf(c_1693,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1689,c_23])).

cnf(c_1694,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1693])).

cnf(c_2188,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1694])).

cnf(c_2657,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2188])).

cnf(c_3449,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,X0,sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2657])).

cnf(c_3499,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,X0,sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3449,c_1285])).

cnf(c_3971,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3499])).

cnf(c_4117,plain,
    ( v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3971,c_27,c_28,c_29,c_34,c_68,c_3769])).

cnf(c_4118,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4117])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3458,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3458,c_0])).

cnf(c_4123,plain,
    ( v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4118,c_3472])).

cnf(c_3129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2665])).

cnf(c_3446,plain,
    ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3129])).

cnf(c_3510,plain,
    ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3446,c_1285])).

cnf(c_4016,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3510])).

cnf(c_4192,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4016])).

cnf(c_4194,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4192,c_27,c_28,c_29,c_34,c_68,c_3769])).

cnf(c_4200,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4194,c_3472])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1322,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_547])).

cnf(c_1323,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1322])).

cnf(c_1327,plain,
    ( v4_orders_2(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_26])).

cnf(c_1328,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1327])).

cnf(c_1658,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1328,c_20])).

cnf(c_1659,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1658])).

cnf(c_1663,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1659,c_23])).

cnf(c_1664,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1663])).

cnf(c_2211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1664])).

cnf(c_2653,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2211])).

cnf(c_3450,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,X0,sK2)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2653])).

cnf(c_3488,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,X0,sK2)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3450,c_1285])).

cnf(c_4024,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3488])).

cnf(c_4203,plain,
    ( v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4024,c_27,c_28,c_29,c_34,c_68,c_3769])).

cnf(c_4204,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4203])).

cnf(c_4209,plain,
    ( v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4204,c_3472])).

cnf(c_4263,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4261,c_27,c_28,c_29,c_34,c_68,c_3554,c_3769,c_4123,c_4200,c_4209])).

cnf(c_4268,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4263,c_3472])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:01:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.08/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.02  
% 2.08/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/1.02  
% 2.08/1.02  ------  iProver source info
% 2.08/1.02  
% 2.08/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.08/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/1.02  git: non_committed_changes: false
% 2.08/1.02  git: last_make_outside_of_git: false
% 2.08/1.02  
% 2.08/1.02  ------ 
% 2.08/1.02  
% 2.08/1.02  ------ Input Options
% 2.08/1.02  
% 2.08/1.02  --out_options                           all
% 2.08/1.02  --tptp_safe_out                         true
% 2.08/1.02  --problem_path                          ""
% 2.08/1.02  --include_path                          ""
% 2.08/1.02  --clausifier                            res/vclausify_rel
% 2.08/1.02  --clausifier_options                    --mode clausify
% 2.08/1.02  --stdin                                 false
% 2.08/1.02  --stats_out                             all
% 2.08/1.02  
% 2.08/1.02  ------ General Options
% 2.08/1.02  
% 2.08/1.02  --fof                                   false
% 2.08/1.02  --time_out_real                         305.
% 2.08/1.02  --time_out_virtual                      -1.
% 2.08/1.02  --symbol_type_check                     false
% 2.08/1.02  --clausify_out                          false
% 2.08/1.02  --sig_cnt_out                           false
% 2.08/1.02  --trig_cnt_out                          false
% 2.08/1.02  --trig_cnt_out_tolerance                1.
% 2.08/1.02  --trig_cnt_out_sk_spl                   false
% 2.08/1.02  --abstr_cl_out                          false
% 2.08/1.02  
% 2.08/1.02  ------ Global Options
% 2.08/1.02  
% 2.08/1.02  --schedule                              default
% 2.08/1.02  --add_important_lit                     false
% 2.08/1.02  --prop_solver_per_cl                    1000
% 2.08/1.02  --min_unsat_core                        false
% 2.08/1.02  --soft_assumptions                      false
% 2.08/1.02  --soft_lemma_size                       3
% 2.08/1.02  --prop_impl_unit_size                   0
% 2.08/1.02  --prop_impl_unit                        []
% 2.08/1.02  --share_sel_clauses                     true
% 2.08/1.02  --reset_solvers                         false
% 2.08/1.02  --bc_imp_inh                            [conj_cone]
% 2.08/1.02  --conj_cone_tolerance                   3.
% 2.08/1.02  --extra_neg_conj                        none
% 2.08/1.02  --large_theory_mode                     true
% 2.08/1.02  --prolific_symb_bound                   200
% 2.08/1.02  --lt_threshold                          2000
% 2.08/1.02  --clause_weak_htbl                      true
% 2.08/1.02  --gc_record_bc_elim                     false
% 2.08/1.02  
% 2.08/1.02  ------ Preprocessing Options
% 2.08/1.02  
% 2.08/1.02  --preprocessing_flag                    true
% 2.08/1.02  --time_out_prep_mult                    0.1
% 2.08/1.02  --splitting_mode                        input
% 2.08/1.02  --splitting_grd                         true
% 2.08/1.02  --splitting_cvd                         false
% 2.08/1.02  --splitting_cvd_svl                     false
% 2.08/1.02  --splitting_nvd                         32
% 2.08/1.02  --sub_typing                            true
% 2.08/1.02  --prep_gs_sim                           true
% 2.08/1.02  --prep_unflatten                        true
% 2.08/1.02  --prep_res_sim                          true
% 2.08/1.02  --prep_upred                            true
% 2.08/1.02  --prep_sem_filter                       exhaustive
% 2.08/1.02  --prep_sem_filter_out                   false
% 2.08/1.02  --pred_elim                             true
% 2.08/1.02  --res_sim_input                         true
% 2.08/1.02  --eq_ax_congr_red                       true
% 2.08/1.02  --pure_diseq_elim                       true
% 2.08/1.02  --brand_transform                       false
% 2.08/1.02  --non_eq_to_eq                          false
% 2.08/1.02  --prep_def_merge                        true
% 2.08/1.02  --prep_def_merge_prop_impl              false
% 2.08/1.02  --prep_def_merge_mbd                    true
% 2.08/1.02  --prep_def_merge_tr_red                 false
% 2.08/1.02  --prep_def_merge_tr_cl                  false
% 2.08/1.02  --smt_preprocessing                     true
% 2.08/1.02  --smt_ac_axioms                         fast
% 2.08/1.02  --preprocessed_out                      false
% 2.08/1.02  --preprocessed_stats                    false
% 2.08/1.02  
% 2.08/1.02  ------ Abstraction refinement Options
% 2.08/1.02  
% 2.08/1.02  --abstr_ref                             []
% 2.08/1.02  --abstr_ref_prep                        false
% 2.08/1.02  --abstr_ref_until_sat                   false
% 2.08/1.02  --abstr_ref_sig_restrict                funpre
% 2.08/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.02  --abstr_ref_under                       []
% 2.08/1.02  
% 2.08/1.02  ------ SAT Options
% 2.08/1.02  
% 2.08/1.02  --sat_mode                              false
% 2.08/1.02  --sat_fm_restart_options                ""
% 2.08/1.02  --sat_gr_def                            false
% 2.08/1.02  --sat_epr_types                         true
% 2.08/1.02  --sat_non_cyclic_types                  false
% 2.08/1.02  --sat_finite_models                     false
% 2.08/1.02  --sat_fm_lemmas                         false
% 2.08/1.02  --sat_fm_prep                           false
% 2.08/1.02  --sat_fm_uc_incr                        true
% 2.08/1.02  --sat_out_model                         small
% 2.08/1.02  --sat_out_clauses                       false
% 2.08/1.02  
% 2.08/1.02  ------ QBF Options
% 2.08/1.02  
% 2.08/1.02  --qbf_mode                              false
% 2.08/1.02  --qbf_elim_univ                         false
% 2.08/1.02  --qbf_dom_inst                          none
% 2.08/1.02  --qbf_dom_pre_inst                      false
% 2.08/1.02  --qbf_sk_in                             false
% 2.08/1.02  --qbf_pred_elim                         true
% 2.08/1.02  --qbf_split                             512
% 2.08/1.02  
% 2.08/1.02  ------ BMC1 Options
% 2.08/1.02  
% 2.08/1.02  --bmc1_incremental                      false
% 2.08/1.02  --bmc1_axioms                           reachable_all
% 2.08/1.02  --bmc1_min_bound                        0
% 2.08/1.02  --bmc1_max_bound                        -1
% 2.08/1.02  --bmc1_max_bound_default                -1
% 2.08/1.02  --bmc1_symbol_reachability              true
% 2.08/1.02  --bmc1_property_lemmas                  false
% 2.08/1.02  --bmc1_k_induction                      false
% 2.08/1.02  --bmc1_non_equiv_states                 false
% 2.08/1.02  --bmc1_deadlock                         false
% 2.08/1.02  --bmc1_ucm                              false
% 2.08/1.02  --bmc1_add_unsat_core                   none
% 2.08/1.02  --bmc1_unsat_core_children              false
% 2.08/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.02  --bmc1_out_stat                         full
% 2.08/1.02  --bmc1_ground_init                      false
% 2.08/1.02  --bmc1_pre_inst_next_state              false
% 2.08/1.02  --bmc1_pre_inst_state                   false
% 2.08/1.02  --bmc1_pre_inst_reach_state             false
% 2.08/1.02  --bmc1_out_unsat_core                   false
% 2.08/1.02  --bmc1_aig_witness_out                  false
% 2.08/1.02  --bmc1_verbose                          false
% 2.08/1.02  --bmc1_dump_clauses_tptp                false
% 2.08/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.02  --bmc1_dump_file                        -
% 2.08/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.02  --bmc1_ucm_extend_mode                  1
% 2.08/1.02  --bmc1_ucm_init_mode                    2
% 2.08/1.02  --bmc1_ucm_cone_mode                    none
% 2.08/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.02  --bmc1_ucm_relax_model                  4
% 2.08/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.02  --bmc1_ucm_layered_model                none
% 2.08/1.02  --bmc1_ucm_max_lemma_size               10
% 2.08/1.02  
% 2.08/1.02  ------ AIG Options
% 2.08/1.02  
% 2.08/1.02  --aig_mode                              false
% 2.08/1.02  
% 2.08/1.02  ------ Instantiation Options
% 2.08/1.02  
% 2.08/1.02  --instantiation_flag                    true
% 2.08/1.02  --inst_sos_flag                         false
% 2.08/1.02  --inst_sos_phase                        true
% 2.08/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.02  --inst_lit_sel_side                     num_symb
% 2.08/1.02  --inst_solver_per_active                1400
% 2.08/1.02  --inst_solver_calls_frac                1.
% 2.08/1.02  --inst_passive_queue_type               priority_queues
% 2.08/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.02  --inst_passive_queues_freq              [25;2]
% 2.08/1.02  --inst_dismatching                      true
% 2.08/1.02  --inst_eager_unprocessed_to_passive     true
% 2.08/1.02  --inst_prop_sim_given                   true
% 2.08/1.02  --inst_prop_sim_new                     false
% 2.08/1.02  --inst_subs_new                         false
% 2.08/1.02  --inst_eq_res_simp                      false
% 2.08/1.02  --inst_subs_given                       false
% 2.08/1.02  --inst_orphan_elimination               true
% 2.08/1.02  --inst_learning_loop_flag               true
% 2.08/1.02  --inst_learning_start                   3000
% 2.08/1.02  --inst_learning_factor                  2
% 2.08/1.02  --inst_start_prop_sim_after_learn       3
% 2.08/1.02  --inst_sel_renew                        solver
% 2.08/1.02  --inst_lit_activity_flag                true
% 2.08/1.02  --inst_restr_to_given                   false
% 2.08/1.02  --inst_activity_threshold               500
% 2.08/1.02  --inst_out_proof                        true
% 2.08/1.02  
% 2.08/1.02  ------ Resolution Options
% 2.08/1.02  
% 2.08/1.02  --resolution_flag                       true
% 2.08/1.02  --res_lit_sel                           adaptive
% 2.08/1.02  --res_lit_sel_side                      none
% 2.08/1.02  --res_ordering                          kbo
% 2.08/1.02  --res_to_prop_solver                    active
% 2.08/1.02  --res_prop_simpl_new                    false
% 2.08/1.02  --res_prop_simpl_given                  true
% 2.08/1.02  --res_passive_queue_type                priority_queues
% 2.08/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.02  --res_passive_queues_freq               [15;5]
% 2.08/1.02  --res_forward_subs                      full
% 2.08/1.02  --res_backward_subs                     full
% 2.08/1.02  --res_forward_subs_resolution           true
% 2.08/1.02  --res_backward_subs_resolution          true
% 2.08/1.02  --res_orphan_elimination                true
% 2.08/1.02  --res_time_limit                        2.
% 2.08/1.02  --res_out_proof                         true
% 2.08/1.02  
% 2.08/1.02  ------ Superposition Options
% 2.08/1.02  
% 2.08/1.02  --superposition_flag                    true
% 2.08/1.02  --sup_passive_queue_type                priority_queues
% 2.08/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.02  --demod_completeness_check              fast
% 2.08/1.02  --demod_use_ground                      true
% 2.08/1.02  --sup_to_prop_solver                    passive
% 2.08/1.02  --sup_prop_simpl_new                    true
% 2.08/1.02  --sup_prop_simpl_given                  true
% 2.08/1.02  --sup_fun_splitting                     false
% 2.08/1.02  --sup_smt_interval                      50000
% 2.08/1.02  
% 2.08/1.02  ------ Superposition Simplification Setup
% 2.08/1.02  
% 2.08/1.02  --sup_indices_passive                   []
% 2.08/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.02  --sup_full_bw                           [BwDemod]
% 2.08/1.02  --sup_immed_triv                        [TrivRules]
% 2.08/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.02  --sup_immed_bw_main                     []
% 2.08/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.02  
% 2.08/1.02  ------ Combination Options
% 2.08/1.02  
% 2.08/1.02  --comb_res_mult                         3
% 2.08/1.02  --comb_sup_mult                         2
% 2.08/1.02  --comb_inst_mult                        10
% 2.08/1.02  
% 2.08/1.02  ------ Debug Options
% 2.08/1.02  
% 2.08/1.02  --dbg_backtrace                         false
% 2.08/1.02  --dbg_dump_prop_clauses                 false
% 2.08/1.02  --dbg_dump_prop_clauses_file            -
% 2.08/1.02  --dbg_out_stat                          false
% 2.08/1.02  ------ Parsing...
% 2.08/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/1.02  
% 2.08/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.08/1.02  
% 2.08/1.02  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/1.02  
% 2.08/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/1.02  ------ Proving...
% 2.08/1.02  ------ Problem Properties 
% 2.08/1.02  
% 2.08/1.02  
% 2.08/1.02  clauses                                 18
% 2.08/1.02  conjectures                             4
% 2.08/1.02  EPR                                     2
% 2.08/1.02  Horn                                    14
% 2.08/1.02  unary                                   10
% 2.08/1.02  binary                                  0
% 2.08/1.02  lits                                    53
% 2.08/1.02  lits eq                                 11
% 2.08/1.02  fd_pure                                 0
% 2.08/1.02  fd_pseudo                               0
% 2.08/1.02  fd_cond                                 0
% 2.08/1.02  fd_pseudo_cond                          0
% 2.08/1.02  AC symbols                              0
% 2.08/1.02  
% 2.08/1.02  ------ Schedule dynamic 5 is on 
% 2.08/1.02  
% 2.08/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/1.02  
% 2.08/1.02  
% 2.08/1.02  ------ 
% 2.08/1.02  Current options:
% 2.08/1.02  ------ 
% 2.08/1.02  
% 2.08/1.02  ------ Input Options
% 2.08/1.02  
% 2.08/1.02  --out_options                           all
% 2.08/1.02  --tptp_safe_out                         true
% 2.08/1.02  --problem_path                          ""
% 2.08/1.02  --include_path                          ""
% 2.08/1.02  --clausifier                            res/vclausify_rel
% 2.08/1.02  --clausifier_options                    --mode clausify
% 2.08/1.02  --stdin                                 false
% 2.08/1.02  --stats_out                             all
% 2.08/1.02  
% 2.08/1.02  ------ General Options
% 2.08/1.02  
% 2.08/1.02  --fof                                   false
% 2.08/1.02  --time_out_real                         305.
% 2.08/1.02  --time_out_virtual                      -1.
% 2.08/1.02  --symbol_type_check                     false
% 2.08/1.02  --clausify_out                          false
% 2.08/1.02  --sig_cnt_out                           false
% 2.08/1.02  --trig_cnt_out                          false
% 2.08/1.02  --trig_cnt_out_tolerance                1.
% 2.08/1.02  --trig_cnt_out_sk_spl                   false
% 2.08/1.02  --abstr_cl_out                          false
% 2.08/1.02  
% 2.08/1.02  ------ Global Options
% 2.08/1.02  
% 2.08/1.02  --schedule                              default
% 2.08/1.02  --add_important_lit                     false
% 2.08/1.02  --prop_solver_per_cl                    1000
% 2.08/1.02  --min_unsat_core                        false
% 2.08/1.02  --soft_assumptions                      false
% 2.08/1.02  --soft_lemma_size                       3
% 2.08/1.02  --prop_impl_unit_size                   0
% 2.08/1.02  --prop_impl_unit                        []
% 2.08/1.02  --share_sel_clauses                     true
% 2.08/1.02  --reset_solvers                         false
% 2.08/1.02  --bc_imp_inh                            [conj_cone]
% 2.08/1.02  --conj_cone_tolerance                   3.
% 2.08/1.02  --extra_neg_conj                        none
% 2.08/1.02  --large_theory_mode                     true
% 2.08/1.02  --prolific_symb_bound                   200
% 2.08/1.02  --lt_threshold                          2000
% 2.08/1.02  --clause_weak_htbl                      true
% 2.08/1.02  --gc_record_bc_elim                     false
% 2.08/1.02  
% 2.08/1.02  ------ Preprocessing Options
% 2.08/1.02  
% 2.08/1.02  --preprocessing_flag                    true
% 2.08/1.02  --time_out_prep_mult                    0.1
% 2.08/1.02  --splitting_mode                        input
% 2.08/1.02  --splitting_grd                         true
% 2.08/1.02  --splitting_cvd                         false
% 2.08/1.02  --splitting_cvd_svl                     false
% 2.08/1.02  --splitting_nvd                         32
% 2.08/1.02  --sub_typing                            true
% 2.08/1.02  --prep_gs_sim                           true
% 2.08/1.02  --prep_unflatten                        true
% 2.08/1.02  --prep_res_sim                          true
% 2.08/1.02  --prep_upred                            true
% 2.08/1.02  --prep_sem_filter                       exhaustive
% 2.08/1.02  --prep_sem_filter_out                   false
% 2.08/1.02  --pred_elim                             true
% 2.08/1.02  --res_sim_input                         true
% 2.08/1.02  --eq_ax_congr_red                       true
% 2.08/1.02  --pure_diseq_elim                       true
% 2.08/1.02  --brand_transform                       false
% 2.08/1.02  --non_eq_to_eq                          false
% 2.08/1.02  --prep_def_merge                        true
% 2.08/1.02  --prep_def_merge_prop_impl              false
% 2.08/1.02  --prep_def_merge_mbd                    true
% 2.08/1.02  --prep_def_merge_tr_red                 false
% 2.08/1.02  --prep_def_merge_tr_cl                  false
% 2.08/1.02  --smt_preprocessing                     true
% 2.08/1.02  --smt_ac_axioms                         fast
% 2.08/1.02  --preprocessed_out                      false
% 2.08/1.02  --preprocessed_stats                    false
% 2.08/1.02  
% 2.08/1.02  ------ Abstraction refinement Options
% 2.08/1.02  
% 2.08/1.02  --abstr_ref                             []
% 2.08/1.02  --abstr_ref_prep                        false
% 2.08/1.02  --abstr_ref_until_sat                   false
% 2.08/1.02  --abstr_ref_sig_restrict                funpre
% 2.08/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.02  --abstr_ref_under                       []
% 2.08/1.02  
% 2.08/1.02  ------ SAT Options
% 2.08/1.02  
% 2.08/1.02  --sat_mode                              false
% 2.08/1.02  --sat_fm_restart_options                ""
% 2.08/1.02  --sat_gr_def                            false
% 2.08/1.02  --sat_epr_types                         true
% 2.08/1.02  --sat_non_cyclic_types                  false
% 2.08/1.02  --sat_finite_models                     false
% 2.08/1.02  --sat_fm_lemmas                         false
% 2.08/1.02  --sat_fm_prep                           false
% 2.08/1.02  --sat_fm_uc_incr                        true
% 2.08/1.02  --sat_out_model                         small
% 2.08/1.02  --sat_out_clauses                       false
% 2.08/1.02  
% 2.08/1.02  ------ QBF Options
% 2.08/1.02  
% 2.08/1.02  --qbf_mode                              false
% 2.08/1.02  --qbf_elim_univ                         false
% 2.08/1.02  --qbf_dom_inst                          none
% 2.08/1.02  --qbf_dom_pre_inst                      false
% 2.08/1.02  --qbf_sk_in                             false
% 2.08/1.02  --qbf_pred_elim                         true
% 2.08/1.02  --qbf_split                             512
% 2.08/1.02  
% 2.08/1.02  ------ BMC1 Options
% 2.08/1.02  
% 2.08/1.02  --bmc1_incremental                      false
% 2.08/1.02  --bmc1_axioms                           reachable_all
% 2.08/1.02  --bmc1_min_bound                        0
% 2.08/1.02  --bmc1_max_bound                        -1
% 2.08/1.02  --bmc1_max_bound_default                -1
% 2.08/1.02  --bmc1_symbol_reachability              true
% 2.08/1.02  --bmc1_property_lemmas                  false
% 2.08/1.02  --bmc1_k_induction                      false
% 2.08/1.02  --bmc1_non_equiv_states                 false
% 2.08/1.02  --bmc1_deadlock                         false
% 2.08/1.02  --bmc1_ucm                              false
% 2.08/1.02  --bmc1_add_unsat_core                   none
% 2.08/1.02  --bmc1_unsat_core_children              false
% 2.08/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.02  --bmc1_out_stat                         full
% 2.08/1.02  --bmc1_ground_init                      false
% 2.08/1.02  --bmc1_pre_inst_next_state              false
% 2.08/1.02  --bmc1_pre_inst_state                   false
% 2.08/1.02  --bmc1_pre_inst_reach_state             false
% 2.08/1.02  --bmc1_out_unsat_core                   false
% 2.08/1.02  --bmc1_aig_witness_out                  false
% 2.08/1.02  --bmc1_verbose                          false
% 2.08/1.02  --bmc1_dump_clauses_tptp                false
% 2.08/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.02  --bmc1_dump_file                        -
% 2.08/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.02  --bmc1_ucm_extend_mode                  1
% 2.08/1.02  --bmc1_ucm_init_mode                    2
% 2.08/1.02  --bmc1_ucm_cone_mode                    none
% 2.08/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.02  --bmc1_ucm_relax_model                  4
% 2.08/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.02  --bmc1_ucm_layered_model                none
% 2.08/1.02  --bmc1_ucm_max_lemma_size               10
% 2.08/1.02  
% 2.08/1.02  ------ AIG Options
% 2.08/1.02  
% 2.08/1.02  --aig_mode                              false
% 2.08/1.02  
% 2.08/1.02  ------ Instantiation Options
% 2.08/1.02  
% 2.08/1.02  --instantiation_flag                    true
% 2.08/1.02  --inst_sos_flag                         false
% 2.08/1.02  --inst_sos_phase                        true
% 2.08/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.02  --inst_lit_sel_side                     none
% 2.08/1.02  --inst_solver_per_active                1400
% 2.08/1.02  --inst_solver_calls_frac                1.
% 2.08/1.02  --inst_passive_queue_type               priority_queues
% 2.08/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.02  --inst_passive_queues_freq              [25;2]
% 2.08/1.02  --inst_dismatching                      true
% 2.08/1.02  --inst_eager_unprocessed_to_passive     true
% 2.08/1.02  --inst_prop_sim_given                   true
% 2.08/1.02  --inst_prop_sim_new                     false
% 2.08/1.02  --inst_subs_new                         false
% 2.08/1.02  --inst_eq_res_simp                      false
% 2.08/1.02  --inst_subs_given                       false
% 2.08/1.02  --inst_orphan_elimination               true
% 2.08/1.02  --inst_learning_loop_flag               true
% 2.08/1.02  --inst_learning_start                   3000
% 2.08/1.02  --inst_learning_factor                  2
% 2.08/1.02  --inst_start_prop_sim_after_learn       3
% 2.08/1.02  --inst_sel_renew                        solver
% 2.08/1.02  --inst_lit_activity_flag                true
% 2.08/1.02  --inst_restr_to_given                   false
% 2.08/1.02  --inst_activity_threshold               500
% 2.08/1.02  --inst_out_proof                        true
% 2.08/1.02  
% 2.08/1.02  ------ Resolution Options
% 2.08/1.02  
% 2.08/1.02  --resolution_flag                       false
% 2.08/1.02  --res_lit_sel                           adaptive
% 2.08/1.02  --res_lit_sel_side                      none
% 2.08/1.02  --res_ordering                          kbo
% 2.08/1.02  --res_to_prop_solver                    active
% 2.08/1.02  --res_prop_simpl_new                    false
% 2.08/1.02  --res_prop_simpl_given                  true
% 2.08/1.02  --res_passive_queue_type                priority_queues
% 2.08/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.02  --res_passive_queues_freq               [15;5]
% 2.08/1.02  --res_forward_subs                      full
% 2.08/1.02  --res_backward_subs                     full
% 2.08/1.02  --res_forward_subs_resolution           true
% 2.08/1.02  --res_backward_subs_resolution          true
% 2.08/1.02  --res_orphan_elimination                true
% 2.08/1.02  --res_time_limit                        2.
% 2.08/1.02  --res_out_proof                         true
% 2.08/1.02  
% 2.08/1.02  ------ Superposition Options
% 2.08/1.02  
% 2.08/1.02  --superposition_flag                    true
% 2.08/1.02  --sup_passive_queue_type                priority_queues
% 2.08/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.02  --demod_completeness_check              fast
% 2.08/1.02  --demod_use_ground                      true
% 2.08/1.02  --sup_to_prop_solver                    passive
% 2.08/1.02  --sup_prop_simpl_new                    true
% 2.08/1.02  --sup_prop_simpl_given                  true
% 2.08/1.02  --sup_fun_splitting                     false
% 2.08/1.02  --sup_smt_interval                      50000
% 2.08/1.02  
% 2.08/1.02  ------ Superposition Simplification Setup
% 2.08/1.02  
% 2.08/1.02  --sup_indices_passive                   []
% 2.08/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.02  --sup_full_bw                           [BwDemod]
% 2.08/1.02  --sup_immed_triv                        [TrivRules]
% 2.08/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.02  --sup_immed_bw_main                     []
% 2.08/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.02  
% 2.08/1.02  ------ Combination Options
% 2.08/1.02  
% 2.08/1.02  --comb_res_mult                         3
% 2.08/1.02  --comb_sup_mult                         2
% 2.08/1.02  --comb_inst_mult                        10
% 2.08/1.02  
% 2.08/1.02  ------ Debug Options
% 2.08/1.02  
% 2.08/1.02  --dbg_backtrace                         false
% 2.08/1.02  --dbg_dump_prop_clauses                 false
% 2.08/1.02  --dbg_dump_prop_clauses_file            -
% 2.08/1.02  --dbg_out_stat                          false
% 2.08/1.02  
% 2.08/1.02  
% 2.08/1.02  
% 2.08/1.02  
% 2.08/1.02  ------ Proving...
% 2.08/1.02  
% 2.08/1.02  
% 2.08/1.02  % SZS status Theorem for theBenchmark.p
% 2.08/1.02  
% 2.08/1.02   Resolution empty clause
% 2.08/1.02  
% 2.08/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/1.02  
% 2.08/1.02  fof(f13,conjecture,(
% 2.08/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f14,negated_conjecture,(
% 2.08/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.08/1.02    inference(negated_conjecture,[],[f13])).
% 2.08/1.02  
% 2.08/1.02  fof(f35,plain,(
% 2.08/1.02    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.08/1.02    inference(ennf_transformation,[],[f14])).
% 2.08/1.02  
% 2.08/1.02  fof(f36,plain,(
% 2.08/1.02    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f35])).
% 2.08/1.02  
% 2.08/1.02  fof(f40,plain,(
% 2.08/1.02    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.08/1.02    inference(nnf_transformation,[],[f36])).
% 2.08/1.02  
% 2.08/1.02  fof(f41,plain,(
% 2.08/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f40])).
% 2.08/1.02  
% 2.08/1.02  fof(f44,plain,(
% 2.08/1.02    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK3) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & (r1_waybel_7(X0,X1,sK3) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.08/1.02    introduced(choice_axiom,[])).
% 2.08/1.02  
% 2.08/1.02  fof(f43,plain,(
% 2.08/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK2,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & (r1_waybel_7(X0,sK2,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2))) )),
% 2.08/1.02    introduced(choice_axiom,[])).
% 2.08/1.02  
% 2.08/1.02  fof(f42,plain,(
% 2.08/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK1,X1,X2) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & (r1_waybel_7(sK1,X1,X2) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.08/1.02    introduced(choice_axiom,[])).
% 2.08/1.02  
% 2.08/1.02  fof(f45,plain,(
% 2.08/1.02    (((~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & (r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.08/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 2.08/1.02  
% 2.08/1.02  fof(f68,plain,(
% 2.08/1.02    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f7,axiom,(
% 2.08/1.02    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f53,plain,(
% 2.08/1.02    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.08/1.02    inference(cnf_transformation,[],[f7])).
% 2.08/1.02  
% 2.08/1.02  fof(f83,plain,(
% 2.08/1.02    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 2.08/1.02    inference(definition_unfolding,[],[f68,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f69,plain,(
% 2.08/1.02    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f82,plain,(
% 2.08/1.02    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 2.08/1.02    inference(definition_unfolding,[],[f69,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f10,axiom,(
% 2.08/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f16,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.08/1.02    inference(pure_predicate_removal,[],[f10])).
% 2.08/1.02  
% 2.08/1.02  fof(f29,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.08/1.02    inference(ennf_transformation,[],[f16])).
% 2.08/1.02  
% 2.08/1.02  fof(f30,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f29])).
% 2.08/1.02  
% 2.08/1.02  fof(f59,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f30])).
% 2.08/1.02  
% 2.08/1.02  fof(f78,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(definition_unfolding,[],[f59,f53,f53,f53,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f67,plain,(
% 2.08/1.02    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f84,plain,(
% 2.08/1.02    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))),
% 2.08/1.02    inference(definition_unfolding,[],[f67,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f66,plain,(
% 2.08/1.02    ~v1_xboole_0(sK2)),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f5,axiom,(
% 2.08/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f22,plain,(
% 2.08/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.08/1.02    inference(ennf_transformation,[],[f5])).
% 2.08/1.02  
% 2.08/1.02  fof(f50,plain,(
% 2.08/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f22])).
% 2.08/1.02  
% 2.08/1.02  fof(f65,plain,(
% 2.08/1.02    l1_pre_topc(sK1)),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f63,plain,(
% 2.08/1.02    ~v2_struct_0(sK1)),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f4,axiom,(
% 2.08/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f21,plain,(
% 2.08/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.08/1.02    inference(ennf_transformation,[],[f4])).
% 2.08/1.02  
% 2.08/1.02  fof(f49,plain,(
% 2.08/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f21])).
% 2.08/1.02  
% 2.08/1.02  fof(f64,plain,(
% 2.08/1.02    v2_pre_topc(sK1)),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f70,plain,(
% 2.08/1.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f81,plain,(
% 2.08/1.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))),
% 2.08/1.02    inference(definition_unfolding,[],[f70,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f6,axiom,(
% 2.08/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f19,plain,(
% 2.08/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.08/1.02    inference(pure_predicate_removal,[],[f6])).
% 2.08/1.02  
% 2.08/1.02  fof(f23,plain,(
% 2.08/1.02    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.08/1.02    inference(ennf_transformation,[],[f19])).
% 2.08/1.02  
% 2.08/1.02  fof(f24,plain,(
% 2.08/1.02    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f23])).
% 2.08/1.02  
% 2.08/1.02  fof(f37,plain,(
% 2.08/1.02    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.08/1.02    introduced(choice_axiom,[])).
% 2.08/1.02  
% 2.08/1.02  fof(f38,plain,(
% 2.08/1.02    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f37])).
% 2.08/1.02  
% 2.08/1.02  fof(f52,plain,(
% 2.08/1.02    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f38])).
% 2.08/1.02  
% 2.08/1.02  fof(f8,axiom,(
% 2.08/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f17,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.08/1.02    inference(pure_predicate_removal,[],[f8])).
% 2.08/1.02  
% 2.08/1.02  fof(f25,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.08/1.02    inference(ennf_transformation,[],[f17])).
% 2.08/1.02  
% 2.08/1.02  fof(f26,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f25])).
% 2.08/1.02  
% 2.08/1.02  fof(f55,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f26])).
% 2.08/1.02  
% 2.08/1.02  fof(f74,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(definition_unfolding,[],[f55,f53,f53,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f73,plain,(
% 2.08/1.02    ~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f11,axiom,(
% 2.08/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f31,plain,(
% 2.08/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.08/1.02    inference(ennf_transformation,[],[f11])).
% 2.08/1.02  
% 2.08/1.02  fof(f32,plain,(
% 2.08/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f31])).
% 2.08/1.02  
% 2.08/1.02  fof(f39,plain,(
% 2.08/1.02    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(nnf_transformation,[],[f32])).
% 2.08/1.02  
% 2.08/1.02  fof(f61,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f39])).
% 2.08/1.02  
% 2.08/1.02  fof(f71,plain,(
% 2.08/1.02    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f12,axiom,(
% 2.08/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f33,plain,(
% 2.08/1.02    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.08/1.02    inference(ennf_transformation,[],[f12])).
% 2.08/1.02  
% 2.08/1.02  fof(f34,plain,(
% 2.08/1.02    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f33])).
% 2.08/1.02  
% 2.08/1.02  fof(f62,plain,(
% 2.08/1.02    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f34])).
% 2.08/1.02  
% 2.08/1.02  fof(f80,plain,(
% 2.08/1.02    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(definition_unfolding,[],[f62,f53,f53,f53,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f72,plain,(
% 2.08/1.02    r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 2.08/1.02    inference(cnf_transformation,[],[f45])).
% 2.08/1.02  
% 2.08/1.02  fof(f60,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f39])).
% 2.08/1.02  
% 2.08/1.02  fof(f51,plain,(
% 2.08/1.02    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f38])).
% 2.08/1.02  
% 2.08/1.02  fof(f3,axiom,(
% 2.08/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f20,plain,(
% 2.08/1.02    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.08/1.02    inference(ennf_transformation,[],[f3])).
% 2.08/1.02  
% 2.08/1.02  fof(f48,plain,(
% 2.08/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f20])).
% 2.08/1.02  
% 2.08/1.02  fof(f58,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f30])).
% 2.08/1.02  
% 2.08/1.02  fof(f79,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(definition_unfolding,[],[f58,f53,f53,f53,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f9,axiom,(
% 2.08/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f15,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.08/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.08/1.02  
% 2.08/1.02  fof(f18,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.08/1.02    inference(pure_predicate_removal,[],[f15])).
% 2.08/1.02  
% 2.08/1.02  fof(f27,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.08/1.02    inference(ennf_transformation,[],[f18])).
% 2.08/1.02  
% 2.08/1.02  fof(f28,plain,(
% 2.08/1.02    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.08/1.02    inference(flattening,[],[f27])).
% 2.08/1.02  
% 2.08/1.02  fof(f56,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f28])).
% 2.08/1.02  
% 2.08/1.02  fof(f77,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(definition_unfolding,[],[f56,f53,f53,f53])).
% 2.08/1.02  
% 2.08/1.02  fof(f2,axiom,(
% 2.08/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f47,plain,(
% 2.08/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.08/1.02    inference(cnf_transformation,[],[f2])).
% 2.08/1.02  
% 2.08/1.02  fof(f1,axiom,(
% 2.08/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 2.08/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.02  
% 2.08/1.02  fof(f46,plain,(
% 2.08/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.08/1.02    inference(cnf_transformation,[],[f1])).
% 2.08/1.02  
% 2.08/1.02  fof(f57,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(cnf_transformation,[],[f28])).
% 2.08/1.02  
% 2.08/1.02  fof(f76,plain,(
% 2.08/1.02    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.08/1.02    inference(definition_unfolding,[],[f57,f53,f53,f53])).
% 2.08/1.02  
% 2.08/1.02  cnf(c_21,negated_conjecture,
% 2.08/1.02      ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.08/1.02      inference(cnf_transformation,[],[f83]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_20,negated_conjecture,
% 2.08/1.02      ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.08/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_11,plain,
% 2.08/1.02      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | v1_xboole_0(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_22,negated_conjecture,
% 2.08/1.02      ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
% 2.08/1.02      inference(cnf_transformation,[],[f84]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_348,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | sK2 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_349,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ l1_struct_0(X1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(sK2)
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_348]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_23,negated_conjecture,
% 2.08/1.02      ( ~ v1_xboole_0(sK2) ),
% 2.08/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_353,plain,
% 2.08/1.02      ( v1_xboole_0(X0)
% 2.08/1.02      | ~ l1_struct_0(X1)
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_349,c_23]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_354,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ l1_struct_0(X1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_353]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_4,plain,
% 2.08/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_24,negated_conjecture,
% 2.08/1.02      ( l1_pre_topc(sK1) ),
% 2.08/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_546,plain,
% 2.08/1.02      ( l1_struct_0(X0) | sK1 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_547,plain,
% 2.08/1.02      ( l1_struct_0(sK1) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_546]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1362,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | sK1 != X1 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_354,c_547]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1363,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_1362]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_26,negated_conjecture,
% 2.08/1.02      ( ~ v2_struct_0(sK1) ),
% 2.08/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1367,plain,
% 2.08/1.02      ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1363,c_26]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1368,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_1367]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1808,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | sK2 != sK2 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_1368]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2086,plain,
% 2.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | sK2 != sK2 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1808]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2669,plain,
% 2.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.08/1.02      inference(equality_resolution_simp,[status(thm)],[c_2086]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3444,plain,
% 2.08/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,X0,sK2)) = iProver_top
% 2.08/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2669]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3,plain,
% 2.08/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1284,plain,
% 2.08/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_547]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1285,plain,
% 2.08/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_1284]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3535,plain,
% 2.08/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,X0,sK2)) = iProver_top
% 2.08/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.02      inference(light_normalisation,[status(thm)],[c_3444,c_1285]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_4114,plain,
% 2.08/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.08/1.02      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.02      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.08/1.02      inference(equality_resolution,[status(thm)],[c_3535]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_4261,plain,
% 2.08/1.02      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.02      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.08/1.02      inference(equality_resolution_simp,[status(thm)],[c_4114]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_27,plain,
% 2.08/1.02      ( v2_struct_0(sK1) != iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_25,negated_conjecture,
% 2.08/1.02      ( v2_pre_topc(sK1) ),
% 2.08/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_28,plain,
% 2.08/1.02      ( v2_pre_topc(sK1) = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_29,plain,
% 2.08/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_19,negated_conjecture,
% 2.08/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
% 2.08/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_34,plain,
% 2.08/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_5,plain,
% 2.08/1.02      ( v2_struct_0(X0)
% 2.08/1.02      | ~ v2_pre_topc(X0)
% 2.08/1.02      | ~ l1_pre_topc(X0)
% 2.08/1.02      | ~ v1_xboole_0(sK0(X0)) ),
% 2.08/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_66,plain,
% 2.08/1.02      ( v2_struct_0(X0) = iProver_top
% 2.08/1.02      | v2_pre_topc(X0) != iProver_top
% 2.08/1.02      | l1_pre_topc(X0) != iProver_top
% 2.08/1.02      | v1_xboole_0(sK0(X0)) != iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_68,plain,
% 2.08/1.02      ( v2_struct_0(sK1) = iProver_top
% 2.08/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.08/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.08/1.02      | v1_xboole_0(sK0(sK1)) != iProver_top ),
% 2.08/1.02      inference(instantiation,[status(thm)],[c_66]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_7,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | v1_xboole_0(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_16,negated_conjecture,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.08/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_191,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.08/1.02      inference(prop_impl,[status(thm)],[c_16]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_13,plain,
% 2.08/1.02      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.08/1.02      | r3_waybel_9(X0,X1,X2)
% 2.08/1.02      | ~ l1_waybel_0(X1,X0)
% 2.08/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.02      | ~ v7_waybel_0(X1)
% 2.08/1.02      | ~ v4_orders_2(X1)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ v2_pre_topc(X0)
% 2.08/1.02      | ~ l1_pre_topc(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_471,plain,
% 2.08/1.02      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.08/1.02      | r3_waybel_9(X0,X1,X2)
% 2.08/1.02      | ~ l1_waybel_0(X1,X0)
% 2.08/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.02      | ~ v7_waybel_0(X1)
% 2.08/1.02      | ~ v4_orders_2(X1)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ l1_pre_topc(X0)
% 2.08/1.02      | sK1 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_472,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.08/1.02      | r3_waybel_9(sK1,X0,X1)
% 2.08/1.02      | ~ l1_waybel_0(X0,sK1)
% 2.08/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(X0)
% 2.08/1.02      | ~ v4_orders_2(X0)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | ~ l1_pre_topc(sK1) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_471]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_476,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.08/1.02      | r3_waybel_9(sK1,X0,X1)
% 2.08/1.02      | ~ l1_waybel_0(X0,sK1)
% 2.08/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(X0)
% 2.08/1.02      | ~ v4_orders_2(X0)
% 2.08/1.02      | v2_struct_0(X0) ),
% 2.08/1.02      inference(global_propositional_subsumption,
% 2.08/1.02                [status(thm)],
% 2.08/1.02                [c_472,c_26,c_24]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_875,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ l1_waybel_0(X0,sK1)
% 2.08/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(X0)
% 2.08/1.02      | ~ v4_orders_2(X0)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 2.08/1.02      | sK3 != X1
% 2.08/1.02      | sK1 != sK1 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_191,c_476]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_876,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.08/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_875]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_18,negated_conjecture,
% 2.08/1.02      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.08/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_878,plain,
% 2.08/1.02      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_876,c_18]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_879,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_878]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_915,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 2.08/1.02      | sK1 != X2 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_879]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_916,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | ~ l1_struct_0(sK1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_915]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_70,plain,
% 2.08/1.02      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.08/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_920,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.08/1.02      inference(global_propositional_subsumption,
% 2.08/1.02                [status(thm)],
% 2.08/1.02                [c_916,c_26,c_24,c_70]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1763,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.08/1.02      | sK2 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_920,c_20]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1764,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(sK2)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_1763]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1768,plain,
% 2.08/1.02      ( v1_xboole_0(X0)
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1764,c_23]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1769,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_1768]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2112,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.02      | sK2 != sK2 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1769]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2665,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(equality_resolution_simp,[status(thm)],[c_2112]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3130,plain,
% 2.08/1.02      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | sP0_iProver_split ),
% 2.08/1.02      inference(splitting,
% 2.08/1.02                [splitting(split),new_symbols(definition,[])],
% 2.08/1.02                [c_2665]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3445,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.02      | sP0_iProver_split = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3130]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_15,plain,
% 2.08/1.02      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ l1_struct_0(X1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.08/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_387,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ l1_struct_0(X1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.08/1.02      | sK2 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_388,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | ~ l1_struct_0(X0)
% 2.08/1.02      | v1_xboole_0(sK2)
% 2.08/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_387]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_392,plain,
% 2.08/1.02      ( ~ l1_struct_0(X0)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_388,c_23]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_393,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | ~ l1_struct_0(X0)
% 2.08/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_392]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1273,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.08/1.02      | sK1 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_393,c_547]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1274,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.08/1.02      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_1273]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1276,plain,
% 2.08/1.02      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 2.08/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.08/1.02      inference(global_propositional_subsumption,
% 2.08/1.02                [status(thm)],
% 2.08/1.02                [c_1274,c_26,c_21,c_20,c_19]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2673,plain,
% 2.08/1.02      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 2.08/1.02      inference(equality_resolution_simp,[status(thm)],[c_1276]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3548,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.02      | sP0_iProver_split = iProver_top ),
% 2.08/1.02      inference(light_normalisation,[status(thm)],[c_3445,c_2673]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_17,negated_conjecture,
% 2.08/1.02      ( r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.08/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_193,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.08/1.02      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_14,plain,
% 2.08/1.02      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.08/1.02      | ~ r3_waybel_9(X0,X1,X2)
% 2.08/1.02      | ~ l1_waybel_0(X1,X0)
% 2.08/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.02      | ~ v7_waybel_0(X1)
% 2.08/1.02      | ~ v4_orders_2(X1)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ v2_pre_topc(X0)
% 2.08/1.02      | ~ l1_pre_topc(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_438,plain,
% 2.08/1.02      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.08/1.02      | ~ r3_waybel_9(X0,X1,X2)
% 2.08/1.02      | ~ l1_waybel_0(X1,X0)
% 2.08/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/1.02      | ~ v7_waybel_0(X1)
% 2.08/1.02      | ~ v4_orders_2(X1)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | v2_struct_0(X1)
% 2.08/1.02      | ~ l1_pre_topc(X0)
% 2.08/1.02      | sK1 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_439,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.08/1.02      | ~ r3_waybel_9(sK1,X0,X1)
% 2.08/1.02      | ~ l1_waybel_0(X0,sK1)
% 2.08/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(X0)
% 2.08/1.02      | ~ v4_orders_2(X0)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | ~ l1_pre_topc(sK1) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_438]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_443,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.08/1.02      | ~ r3_waybel_9(sK1,X0,X1)
% 2.08/1.02      | ~ l1_waybel_0(X0,sK1)
% 2.08/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(X0)
% 2.08/1.02      | ~ v4_orders_2(X0)
% 2.08/1.02      | v2_struct_0(X0) ),
% 2.08/1.02      inference(global_propositional_subsumption,
% 2.08/1.02                [status(thm)],
% 2.08/1.02                [c_439,c_26,c_24]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_849,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ l1_waybel_0(X0,sK1)
% 2.08/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(X0)
% 2.08/1.02      | ~ v4_orders_2(X0)
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 2.08/1.02      | sK3 != X1
% 2.08/1.02      | sK1 != sK1 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_193,c_443]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_850,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.08/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_849]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_852,plain,
% 2.08/1.02      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_850,c_18]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_853,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_852]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_963,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 2.08/1.02      | sK1 != X2 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_853]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_964,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | ~ l1_struct_0(sK1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_963]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_968,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.08/1.02      inference(global_propositional_subsumption,
% 2.08/1.02                [status(thm)],
% 2.08/1.02                [c_964,c_26,c_24,c_70]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1718,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.08/1.02      | sK2 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_968,c_20]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1719,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(sK2)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_1718]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1723,plain,
% 2.08/1.02      ( v1_xboole_0(X0)
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1719,c_23]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1724,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_1723]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2150,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.02      | sK2 != sK2 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1724]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2661,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(equality_resolution_simp,[status(thm)],[c_2150]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3131,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3)
% 2.08/1.02      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.08/1.02      | sP0_iProver_split ),
% 2.08/1.02      inference(splitting,
% 2.08/1.02                [splitting(split),new_symbols(definition,[])],
% 2.08/1.02                [c_2661]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3447,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
% 2.08/1.02      | r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.02      | sP0_iProver_split = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_3131]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3524,plain,
% 2.08/1.02      ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 2.08/1.02      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.02      | sP0_iProver_split = iProver_top ),
% 2.08/1.02      inference(light_normalisation,[status(thm)],[c_3447,c_2673]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3554,plain,
% 2.08/1.02      ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.02      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.02      | sP0_iProver_split = iProver_top ),
% 2.08/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_3548,c_3524]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_6,plain,
% 2.08/1.02      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | ~ v2_pre_topc(X0)
% 2.08/1.02      | ~ l1_pre_topc(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_504,plain,
% 2.08/1.02      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.08/1.02      | v2_struct_0(X0)
% 2.08/1.02      | ~ l1_pre_topc(X0)
% 2.08/1.02      | sK1 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_505,plain,
% 2.08/1.02      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | ~ l1_pre_topc(sK1) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_504]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_64,plain,
% 2.08/1.02      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | ~ v2_pre_topc(sK1)
% 2.08/1.02      | ~ l1_pre_topc(sK1) ),
% 2.08/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_507,plain,
% 2.08/1.02      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.08/1.02      inference(global_propositional_subsumption,
% 2.08/1.02                [status(thm)],
% 2.08/1.02                [c_505,c_26,c_25,c_24,c_64]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3452,plain,
% 2.08/1.02      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3475,plain,
% 2.08/1.02      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.08/1.02      inference(light_normalisation,[status(thm)],[c_3452,c_1285]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_2,plain,
% 2.08/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.08/1.02      | ~ v1_xboole_0(X1)
% 2.08/1.02      | v1_xboole_0(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3457,plain,
% 2.08/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.08/1.02      | v1_xboole_0(X1) != iProver_top
% 2.08/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_3769,plain,
% 2.08/1.02      ( v1_xboole_0(sK0(sK1)) = iProver_top
% 2.08/1.02      | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.08/1.02      inference(superposition,[status(thm)],[c_3475,c_3457]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_12,plain,
% 2.08/1.02      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | v1_xboole_0(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_10,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | v1_xboole_0(X0) ),
% 2.08/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_147,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | v1_xboole_0(X0) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_12,c_10]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_148,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.08/1.02      | ~ l1_struct_0(X2)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_147]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1289,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | v2_struct_0(X2)
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | sK1 != X2 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_148,c_547]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1290,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.08/1.02      | v2_struct_0(sK1)
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_1289]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1294,plain,
% 2.08/1.02      ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1290,c_26]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1295,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1) ),
% 2.08/1.02      inference(renaming,[status(thm)],[c_1294]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1688,plain,
% 2.08/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(X1)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.08/1.02      | sK2 != X0 ),
% 2.08/1.02      inference(resolution_lifted,[status(thm)],[c_1295,c_20]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1689,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | v1_xboole_0(X0)
% 2.08/1.02      | v1_xboole_0(sK2)
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(unflattening,[status(thm)],[c_1688]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1693,plain,
% 2.08/1.02      ( v1_xboole_0(X0)
% 2.08/1.02      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1689,c_23]) ).
% 2.08/1.02  
% 2.08/1.02  cnf(c_1694,plain,
% 2.08/1.02      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.03      inference(renaming,[status(thm)],[c_1693]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2188,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | sK2 != sK2 ),
% 2.08/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_1694]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2657,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.03      inference(equality_resolution_simp,[status(thm)],[c_2188]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3449,plain,
% 2.08/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.03      | v2_struct_0(k3_yellow19(sK1,X0,sK2)) != iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_2657]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3499,plain,
% 2.08/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.03      | v2_struct_0(k3_yellow19(sK1,X0,sK2)) != iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.03      inference(light_normalisation,[status(thm)],[c_3449,c_1285]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3971,plain,
% 2.08/1.03      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.08/1.03      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.03      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.08/1.03      inference(equality_resolution,[status(thm)],[c_3499]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4117,plain,
% 2.08/1.03      ( v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.08/1.03      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.08/1.03      inference(global_propositional_subsumption,
% 2.08/1.03                [status(thm)],
% 2.08/1.03                [c_3971,c_27,c_28,c_29,c_34,c_68,c_3769]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4118,plain,
% 2.08/1.03      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.08/1.03      inference(renaming,[status(thm)],[c_4117]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1,plain,
% 2.08/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.08/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3458,plain,
% 2.08/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_0,plain,
% 2.08/1.03      ( k2_subset_1(X0) = X0 ),
% 2.08/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3472,plain,
% 2.08/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.08/1.03      inference(light_normalisation,[status(thm)],[c_3458,c_0]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4123,plain,
% 2.08/1.03      ( v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.08/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4118,c_3472]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3129,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | ~ sP0_iProver_split ),
% 2.08/1.03      inference(splitting,
% 2.08/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.08/1.03                [c_2665]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3446,plain,
% 2.08/1.03      ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top
% 2.08/1.03      | sP0_iProver_split != iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_3129]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3510,plain,
% 2.08/1.03      ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top
% 2.08/1.03      | sP0_iProver_split != iProver_top ),
% 2.08/1.03      inference(light_normalisation,[status(thm)],[c_3446,c_1285]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4016,plain,
% 2.08/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.08/1.03      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.08/1.03      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 2.08/1.03      | sP0_iProver_split != iProver_top ),
% 2.08/1.03      inference(equality_resolution,[status(thm)],[c_3510]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4192,plain,
% 2.08/1.03      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.08/1.03      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 2.08/1.03      | sP0_iProver_split != iProver_top ),
% 2.08/1.03      inference(equality_resolution_simp,[status(thm)],[c_4016]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4194,plain,
% 2.08/1.03      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | sP0_iProver_split != iProver_top ),
% 2.08/1.03      inference(global_propositional_subsumption,
% 2.08/1.03                [status(thm)],
% 2.08/1.03                [c_4192,c_27,c_28,c_29,c_34,c_68,c_3769]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4200,plain,
% 2.08/1.03      ( sP0_iProver_split != iProver_top ),
% 2.08/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4194,c_3472]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_9,plain,
% 2.08/1.03      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.03      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.08/1.03      | v2_struct_0(X2)
% 2.08/1.03      | ~ l1_struct_0(X2)
% 2.08/1.03      | v1_xboole_0(X1)
% 2.08/1.03      | v1_xboole_0(X0) ),
% 2.08/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1322,plain,
% 2.08/1.03      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.03      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.08/1.03      | v2_struct_0(X2)
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1)
% 2.08/1.03      | sK1 != X2 ),
% 2.08/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_547]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1323,plain,
% 2.08/1.03      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.08/1.03      | v2_struct_0(sK1)
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1) ),
% 2.08/1.03      inference(unflattening,[status(thm)],[c_1322]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1327,plain,
% 2.08/1.03      ( v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.08/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.03      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1) ),
% 2.08/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1323,c_26]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1328,plain,
% 2.08/1.03      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1) ),
% 2.08/1.03      inference(renaming,[status(thm)],[c_1327]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1658,plain,
% 2.08/1.03      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.08/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.08/1.03      | sK2 != X0 ),
% 2.08/1.03      inference(resolution_lifted,[status(thm)],[c_1328,c_20]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1659,plain,
% 2.08/1.03      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(sK2)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.03      inference(unflattening,[status(thm)],[c_1658]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1663,plain,
% 2.08/1.03      ( v1_xboole_0(X0)
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1659,c_23]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1664,plain,
% 2.08/1.03      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.03      inference(renaming,[status(thm)],[c_1663]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2211,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | sK2 != sK2 ),
% 2.08/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_1664]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2653,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.08/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.08/1.03      inference(equality_resolution_simp,[status(thm)],[c_2211]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3450,plain,
% 2.08/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X0,sK2)) = iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_2653]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3488,plain,
% 2.08/1.03      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.08/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,X0,sK2)) = iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.03      inference(light_normalisation,[status(thm)],[c_3450,c_1285]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4024,plain,
% 2.08/1.03      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.03      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.08/1.03      inference(equality_resolution,[status(thm)],[c_3488]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4203,plain,
% 2.08/1.03      ( v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.08/1.03      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.08/1.03      inference(global_propositional_subsumption,
% 2.08/1.03                [status(thm)],
% 2.08/1.03                [c_4024,c_27,c_28,c_29,c_34,c_68,c_3769]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4204,plain,
% 2.08/1.03      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.08/1.03      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.08/1.03      inference(renaming,[status(thm)],[c_4203]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4209,plain,
% 2.08/1.03      ( v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.08/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4204,c_3472]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4263,plain,
% 2.08/1.03      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.08/1.03      inference(global_propositional_subsumption,
% 2.08/1.03                [status(thm)],
% 2.08/1.03                [c_4261,c_27,c_28,c_29,c_34,c_68,c_3554,c_3769,c_4123,c_4200,
% 2.08/1.03                 c_4209]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_4268,plain,
% 2.08/1.03      ( $false ),
% 2.08/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4263,c_3472]) ).
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/1.03  
% 2.08/1.03  ------                               Statistics
% 2.08/1.03  
% 2.08/1.03  ------ General
% 2.08/1.03  
% 2.08/1.03  abstr_ref_over_cycles:                  0
% 2.08/1.03  abstr_ref_under_cycles:                 0
% 2.08/1.03  gc_basic_clause_elim:                   0
% 2.08/1.03  forced_gc_time:                         0
% 2.08/1.03  parsing_time:                           0.015
% 2.08/1.03  unif_index_cands_time:                  0.
% 2.08/1.03  unif_index_add_time:                    0.
% 2.08/1.03  orderings_time:                         0.
% 2.08/1.03  out_proof_time:                         0.018
% 2.08/1.03  total_time:                             0.181
% 2.08/1.03  num_of_symbols:                         58
% 2.08/1.03  num_of_terms:                           1912
% 2.08/1.03  
% 2.08/1.03  ------ Preprocessing
% 2.08/1.03  
% 2.08/1.03  num_of_splits:                          2
% 2.08/1.03  num_of_split_atoms:                     1
% 2.08/1.03  num_of_reused_defs:                     1
% 2.08/1.03  num_eq_ax_congr_red:                    7
% 2.08/1.03  num_of_sem_filtered_clauses:            1
% 2.08/1.03  num_of_subtypes:                        0
% 2.08/1.03  monotx_restored_types:                  0
% 2.08/1.03  sat_num_of_epr_types:                   0
% 2.08/1.03  sat_num_of_non_cyclic_types:            0
% 2.08/1.03  sat_guarded_non_collapsed_types:        0
% 2.08/1.03  num_pure_diseq_elim:                    0
% 2.08/1.03  simp_replaced_by:                       0
% 2.08/1.03  res_preprocessed:                       109
% 2.08/1.03  prep_upred:                             0
% 2.08/1.03  prep_unflattend:                        31
% 2.08/1.03  smt_new_axioms:                         0
% 2.08/1.03  pred_elim_cands:                        6
% 2.08/1.03  pred_elim:                              8
% 2.08/1.03  pred_elim_cl:                           10
% 2.08/1.03  pred_elim_cycles:                       23
% 2.08/1.03  merged_defs:                            2
% 2.08/1.03  merged_defs_ncl:                        0
% 2.08/1.03  bin_hyper_res:                          2
% 2.08/1.03  prep_cycles:                            4
% 2.08/1.03  pred_elim_time:                         0.086
% 2.08/1.03  splitting_time:                         0.
% 2.08/1.03  sem_filter_time:                        0.
% 2.08/1.03  monotx_time:                            0.
% 2.08/1.03  subtype_inf_time:                       0.
% 2.08/1.03  
% 2.08/1.03  ------ Problem properties
% 2.08/1.03  
% 2.08/1.03  clauses:                                18
% 2.08/1.03  conjectures:                            4
% 2.08/1.03  epr:                                    2
% 2.08/1.03  horn:                                   14
% 2.08/1.03  ground:                                 10
% 2.08/1.03  unary:                                  10
% 2.08/1.03  binary:                                 0
% 2.08/1.03  lits:                                   53
% 2.08/1.03  lits_eq:                                11
% 2.08/1.03  fd_pure:                                0
% 2.08/1.03  fd_pseudo:                              0
% 2.08/1.03  fd_cond:                                0
% 2.08/1.03  fd_pseudo_cond:                         0
% 2.08/1.03  ac_symbols:                             0
% 2.08/1.03  
% 2.08/1.03  ------ Propositional Solver
% 2.08/1.03  
% 2.08/1.03  prop_solver_calls:                      26
% 2.08/1.03  prop_fast_solver_calls:                 1660
% 2.08/1.03  smt_solver_calls:                       0
% 2.08/1.03  smt_fast_solver_calls:                  0
% 2.08/1.03  prop_num_of_clauses:                    791
% 2.08/1.03  prop_preprocess_simplified:             3146
% 2.08/1.03  prop_fo_subsumed:                       47
% 2.08/1.03  prop_solver_time:                       0.
% 2.08/1.03  smt_solver_time:                        0.
% 2.08/1.03  smt_fast_solver_time:                   0.
% 2.08/1.03  prop_fast_solver_time:                  0.
% 2.08/1.03  prop_unsat_core_time:                   0.
% 2.08/1.03  
% 2.08/1.03  ------ QBF
% 2.08/1.03  
% 2.08/1.03  qbf_q_res:                              0
% 2.08/1.03  qbf_num_tautologies:                    0
% 2.08/1.03  qbf_prep_cycles:                        0
% 2.08/1.03  
% 2.08/1.03  ------ BMC1
% 2.08/1.03  
% 2.08/1.03  bmc1_current_bound:                     -1
% 2.08/1.03  bmc1_last_solved_bound:                 -1
% 2.08/1.03  bmc1_unsat_core_size:                   -1
% 2.08/1.03  bmc1_unsat_core_parents_size:           -1
% 2.08/1.03  bmc1_merge_next_fun:                    0
% 2.08/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.08/1.03  
% 2.08/1.03  ------ Instantiation
% 2.08/1.03  
% 2.08/1.03  inst_num_of_clauses:                    156
% 2.08/1.03  inst_num_in_passive:                    33
% 2.08/1.03  inst_num_in_active:                     107
% 2.08/1.03  inst_num_in_unprocessed:                16
% 2.08/1.03  inst_num_of_loops:                      110
% 2.08/1.03  inst_num_of_learning_restarts:          0
% 2.08/1.03  inst_num_moves_active_passive:          1
% 2.08/1.03  inst_lit_activity:                      0
% 2.08/1.03  inst_lit_activity_moves:                0
% 2.08/1.03  inst_num_tautologies:                   0
% 2.08/1.03  inst_num_prop_implied:                  0
% 2.08/1.03  inst_num_existing_simplified:           0
% 2.08/1.03  inst_num_eq_res_simplified:             0
% 2.08/1.03  inst_num_child_elim:                    0
% 2.08/1.03  inst_num_of_dismatching_blockings:      35
% 2.08/1.03  inst_num_of_non_proper_insts:           111
% 2.08/1.03  inst_num_of_duplicates:                 0
% 2.08/1.03  inst_inst_num_from_inst_to_res:         0
% 2.08/1.03  inst_dismatching_checking_time:         0.
% 2.08/1.03  
% 2.08/1.03  ------ Resolution
% 2.08/1.03  
% 2.08/1.03  res_num_of_clauses:                     0
% 2.08/1.03  res_num_in_passive:                     0
% 2.08/1.03  res_num_in_active:                      0
% 2.08/1.03  res_num_of_loops:                       113
% 2.08/1.03  res_forward_subset_subsumed:            12
% 2.08/1.03  res_backward_subset_subsumed:           0
% 2.08/1.03  res_forward_subsumed:                   1
% 2.08/1.03  res_backward_subsumed:                  0
% 2.08/1.03  res_forward_subsumption_resolution:     2
% 2.08/1.03  res_backward_subsumption_resolution:    0
% 2.08/1.03  res_clause_to_clause_subsumption:       350
% 2.08/1.03  res_orphan_elimination:                 0
% 2.08/1.03  res_tautology_del:                      20
% 2.08/1.03  res_num_eq_res_simplified:              6
% 2.08/1.03  res_num_sel_changes:                    0
% 2.08/1.03  res_moves_from_active_to_pass:          0
% 2.08/1.03  
% 2.08/1.03  ------ Superposition
% 2.08/1.03  
% 2.08/1.03  sup_time_total:                         0.
% 2.08/1.03  sup_time_generating:                    0.
% 2.08/1.03  sup_time_sim_full:                      0.
% 2.08/1.03  sup_time_sim_immed:                     0.
% 2.08/1.03  
% 2.08/1.03  sup_num_of_clauses:                     22
% 2.08/1.03  sup_num_in_active:                      21
% 2.08/1.03  sup_num_in_passive:                     1
% 2.08/1.03  sup_num_of_loops:                       21
% 2.08/1.03  sup_fw_superposition:                   2
% 2.08/1.03  sup_bw_superposition:                   1
% 2.08/1.03  sup_immediate_simplified:               0
% 2.08/1.03  sup_given_eliminated:                   0
% 2.08/1.03  comparisons_done:                       0
% 2.08/1.03  comparisons_avoided:                    0
% 2.08/1.03  
% 2.08/1.03  ------ Simplifications
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  sim_fw_subset_subsumed:                 0
% 2.08/1.03  sim_bw_subset_subsumed:                 0
% 2.08/1.03  sim_fw_subsumed:                        0
% 2.08/1.03  sim_bw_subsumed:                        1
% 2.08/1.03  sim_fw_subsumption_res:                 5
% 2.08/1.03  sim_bw_subsumption_res:                 0
% 2.08/1.03  sim_tautology_del:                      1
% 2.08/1.03  sim_eq_tautology_del:                   0
% 2.08/1.03  sim_eq_res_simp:                        2
% 2.08/1.03  sim_fw_demodulated:                     0
% 2.08/1.03  sim_bw_demodulated:                     0
% 2.08/1.03  sim_light_normalised:                   10
% 2.08/1.03  sim_joinable_taut:                      0
% 2.08/1.03  sim_joinable_simp:                      0
% 2.08/1.03  sim_ac_normalised:                      0
% 2.08/1.03  sim_smt_subsumption:                    0
% 2.08/1.03  
%------------------------------------------------------------------------------
