%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:19 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  217 (1618 expanded)
%              Number of clauses        :  131 ( 310 expanded)
%              Number of leaves         :   19 ( 466 expanded)
%              Depth                    :   28
%              Number of atoms          : 1323 (14755 expanded)
%              Number of equality atoms :  238 ( 530 expanded)
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
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_waybel_7(X0,X1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & ( r2_waybel_7(X0,X1,X2)
            | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_waybel_7(X0,X1,sK4)
          | ~ r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & ( r2_waybel_7(X0,X1,sK4)
          | r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
            ( ( ~ r2_waybel_7(X0,sK3,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3))) )
            & ( r2_waybel_7(X0,sK3,X2)
              | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3))) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
              ( ( ~ r2_waybel_7(sK2,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1))) )
              & ( r2_waybel_7(sK2,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1))) )
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

fof(f50,plain,
    ( ( ~ r2_waybel_7(sK2,sK3,sK4)
      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) )
    & ( r2_waybel_7(sK2,sK3,sK4)
      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f49,f48,f47])).

fof(f75,plain,(
    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,(
    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f75,f60])).

fof(f76,plain,(
    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f76,f60])).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f30])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
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
    inference(definition_unfolding,[],[f66,f60,f60,f60,f60])).

fof(f74,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(definition_unfolding,[],[f74,f60])).

fof(f73,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f26])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
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
    inference(definition_unfolding,[],[f61,f60,f60,f60])).

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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f28])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
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
    inference(definition_unfolding,[],[f64,f60,f60,f60])).

fof(f80,plain,
    ( ~ r2_waybel_7(sK2,sK3,sK4)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
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
    inference(definition_unfolding,[],[f62,f60,f60,f60])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f60,f60,f60,f60])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(definition_unfolding,[],[f77,f60])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f42])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,
    ( r2_waybel_7(sK2,sK3,sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

cnf(c_23,negated_conjecture,
    ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_22,negated_conjecture,
    ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_24,negated_conjecture,
    ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_374,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_375,plain,
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
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_379,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_25])).

cnf(c_380,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_379])).

cnf(c_1359,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_380])).

cnf(c_1752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1359])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_572,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_26])).

cnf(c_573,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_2118,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1752,c_573])).

cnf(c_2119,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_2118])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2123,plain,
    ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2119,c_28])).

cnf(c_2124,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_2123])).

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
    inference(cnf_transformation,[],[f82])).

cnf(c_1287,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_1288,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1287])).

cnf(c_1292,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1288,c_25])).

cnf(c_1293,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1292])).

cnf(c_1813,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1293])).

cnf(c_2091,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1813,c_573])).

cnf(c_2092,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2091])).

cnf(c_2096,plain,
    ( ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2092,c_28])).

cnf(c_2097,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2096])).

cnf(c_11,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1251,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_1252,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1251])).

cnf(c_1256,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_25])).

cnf(c_1257,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1256])).

cnf(c_1842,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1257])).

cnf(c_2064,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1842,c_573])).

cnf(c_2065,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2064])).

cnf(c_2069,plain,
    ( v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2065,c_28])).

cnf(c_2070,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2069])).

cnf(c_18,negated_conjecture,
    ( ~ r2_waybel_7(sK2,sK3,sK4)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_210,plain,
    ( ~ r2_waybel_7(sK2,sK3,sK4)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_464,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_465,plain,
    ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_469,plain,
    ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_28,c_26])).

cnf(c_908,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_210,c_469])).

cnf(c_909,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_913,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_20])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1323,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_1324,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1323])).

cnf(c_1328,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_25])).

cnf(c_1329,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1328])).

cnf(c_1784,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK3),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1329])).

cnf(c_1942,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X2))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(X1,X0,sK3) != X2
    | k2_yellow19(sK2,X2) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_913,c_1784])).

cnf(c_1943,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1942])).

cnf(c_72,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1947,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1943,c_28,c_26,c_72])).

cnf(c_2154,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2070,c_1947])).

cnf(c_2169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2097,c_2154])).

cnf(c_2186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2124,c_2169])).

cnf(c_3233,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2186])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2059,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_573])).

cnf(c_2060,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2059])).

cnf(c_3295,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3233,c_2060])).

cnf(c_3486,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3295])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_413,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_414,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK3)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_418,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_25])).

cnf(c_419,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(renaming,[status(thm)],[c_418])).

cnf(c_1394,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_419])).

cnf(c_1871,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1394])).

cnf(c_2048,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != sK3
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1871,c_573])).

cnf(c_2049,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v2_struct_0(sK2)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_2048])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_421,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_2051,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2049,c_28,c_26,c_23,c_22,c_21,c_72,c_421])).

cnf(c_2611,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_2051])).

cnf(c_3487,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | sK3 != sK3
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3486,c_2611])).

cnf(c_3488,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3487])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_68,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_70,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_19,negated_conjecture,
    ( r2_waybel_7(sK2,sK3,sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_212,plain,
    ( r2_waybel_7(sK2,sK3,sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_497,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_498,plain,
    ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_502,plain,
    ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_28,c_26])).

cnf(c_875,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,X0))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_502])).

cnf(c_876,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(unflattening,[status(thm)],[c_875])).

cnf(c_880,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_876,c_20])).

cnf(c_1984,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,X2))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(X1,X0,sK3) != X2
    | k2_yellow19(sK2,X2) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_880,c_1784])).

cnf(c_1985,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1984])).

cnf(c_1989,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1985,c_28,c_26,c_72])).

cnf(c_2155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2070,c_1989])).

cnf(c_2168,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2097,c_2155])).

cnf(c_2215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2124,c_2168])).

cnf(c_3232,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2215])).

cnf(c_3278,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3232,c_2060])).

cnf(c_3828,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3278])).

cnf(c_3829,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | sK3 != sK3
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3828,c_2611])).

cnf(c_3830,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3829])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3242,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_530,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_531,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_66,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_533,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_28,c_27,c_26,c_66])).

cnf(c_3235,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_3257,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3235,c_2060])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3570,plain,
    ( r2_hidden(X0,sK1(sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3257,c_3239])).

cnf(c_3835,plain,
    ( v1_xboole_0(sK1(sK2)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3242,c_3570])).

cnf(c_3892,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3488,c_29,c_30,c_31,c_36,c_70,c_3830,c_3835])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3240,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3240,c_2])).

cnf(c_3897,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3892,c_3254])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.99/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.99/1.07  
% 0.99/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/1.07  
% 0.99/1.07  ------  iProver source info
% 0.99/1.07  
% 0.99/1.07  git: date: 2020-06-30 10:37:57 +0100
% 0.99/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/1.07  git: non_committed_changes: false
% 0.99/1.07  git: last_make_outside_of_git: false
% 0.99/1.07  
% 0.99/1.07  ------ 
% 0.99/1.07  
% 0.99/1.07  ------ Input Options
% 0.99/1.07  
% 0.99/1.07  --out_options                           all
% 0.99/1.07  --tptp_safe_out                         true
% 0.99/1.07  --problem_path                          ""
% 0.99/1.07  --include_path                          ""
% 0.99/1.07  --clausifier                            res/vclausify_rel
% 0.99/1.07  --clausifier_options                    --mode clausify
% 0.99/1.07  --stdin                                 false
% 0.99/1.07  --stats_out                             all
% 0.99/1.07  
% 0.99/1.07  ------ General Options
% 0.99/1.07  
% 0.99/1.07  --fof                                   false
% 0.99/1.07  --time_out_real                         305.
% 0.99/1.07  --time_out_virtual                      -1.
% 0.99/1.07  --symbol_type_check                     false
% 0.99/1.07  --clausify_out                          false
% 0.99/1.07  --sig_cnt_out                           false
% 0.99/1.07  --trig_cnt_out                          false
% 0.99/1.07  --trig_cnt_out_tolerance                1.
% 0.99/1.07  --trig_cnt_out_sk_spl                   false
% 0.99/1.07  --abstr_cl_out                          false
% 0.99/1.07  
% 0.99/1.07  ------ Global Options
% 0.99/1.07  
% 0.99/1.07  --schedule                              default
% 0.99/1.07  --add_important_lit                     false
% 0.99/1.07  --prop_solver_per_cl                    1000
% 0.99/1.07  --min_unsat_core                        false
% 0.99/1.07  --soft_assumptions                      false
% 0.99/1.07  --soft_lemma_size                       3
% 0.99/1.07  --prop_impl_unit_size                   0
% 0.99/1.07  --prop_impl_unit                        []
% 0.99/1.07  --share_sel_clauses                     true
% 0.99/1.07  --reset_solvers                         false
% 0.99/1.07  --bc_imp_inh                            [conj_cone]
% 0.99/1.07  --conj_cone_tolerance                   3.
% 0.99/1.07  --extra_neg_conj                        none
% 0.99/1.07  --large_theory_mode                     true
% 0.99/1.07  --prolific_symb_bound                   200
% 0.99/1.07  --lt_threshold                          2000
% 0.99/1.07  --clause_weak_htbl                      true
% 0.99/1.07  --gc_record_bc_elim                     false
% 0.99/1.07  
% 0.99/1.07  ------ Preprocessing Options
% 0.99/1.07  
% 0.99/1.07  --preprocessing_flag                    true
% 0.99/1.07  --time_out_prep_mult                    0.1
% 0.99/1.07  --splitting_mode                        input
% 0.99/1.07  --splitting_grd                         true
% 0.99/1.07  --splitting_cvd                         false
% 0.99/1.07  --splitting_cvd_svl                     false
% 0.99/1.07  --splitting_nvd                         32
% 0.99/1.07  --sub_typing                            true
% 0.99/1.07  --prep_gs_sim                           true
% 0.99/1.07  --prep_unflatten                        true
% 0.99/1.07  --prep_res_sim                          true
% 0.99/1.07  --prep_upred                            true
% 0.99/1.07  --prep_sem_filter                       exhaustive
% 0.99/1.07  --prep_sem_filter_out                   false
% 0.99/1.07  --pred_elim                             true
% 0.99/1.07  --res_sim_input                         true
% 0.99/1.07  --eq_ax_congr_red                       true
% 0.99/1.07  --pure_diseq_elim                       true
% 0.99/1.07  --brand_transform                       false
% 0.99/1.07  --non_eq_to_eq                          false
% 0.99/1.07  --prep_def_merge                        true
% 0.99/1.07  --prep_def_merge_prop_impl              false
% 0.99/1.07  --prep_def_merge_mbd                    true
% 0.99/1.07  --prep_def_merge_tr_red                 false
% 0.99/1.07  --prep_def_merge_tr_cl                  false
% 0.99/1.07  --smt_preprocessing                     true
% 0.99/1.07  --smt_ac_axioms                         fast
% 0.99/1.07  --preprocessed_out                      false
% 0.99/1.07  --preprocessed_stats                    false
% 0.99/1.07  
% 0.99/1.07  ------ Abstraction refinement Options
% 0.99/1.07  
% 0.99/1.07  --abstr_ref                             []
% 0.99/1.07  --abstr_ref_prep                        false
% 0.99/1.07  --abstr_ref_until_sat                   false
% 0.99/1.07  --abstr_ref_sig_restrict                funpre
% 0.99/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.07  --abstr_ref_under                       []
% 0.99/1.07  
% 0.99/1.07  ------ SAT Options
% 0.99/1.07  
% 0.99/1.07  --sat_mode                              false
% 0.99/1.07  --sat_fm_restart_options                ""
% 0.99/1.07  --sat_gr_def                            false
% 0.99/1.07  --sat_epr_types                         true
% 0.99/1.07  --sat_non_cyclic_types                  false
% 0.99/1.07  --sat_finite_models                     false
% 0.99/1.07  --sat_fm_lemmas                         false
% 0.99/1.07  --sat_fm_prep                           false
% 0.99/1.07  --sat_fm_uc_incr                        true
% 0.99/1.07  --sat_out_model                         small
% 0.99/1.07  --sat_out_clauses                       false
% 0.99/1.07  
% 0.99/1.07  ------ QBF Options
% 0.99/1.07  
% 0.99/1.07  --qbf_mode                              false
% 0.99/1.07  --qbf_elim_univ                         false
% 0.99/1.07  --qbf_dom_inst                          none
% 0.99/1.07  --qbf_dom_pre_inst                      false
% 0.99/1.07  --qbf_sk_in                             false
% 0.99/1.07  --qbf_pred_elim                         true
% 0.99/1.07  --qbf_split                             512
% 0.99/1.07  
% 0.99/1.07  ------ BMC1 Options
% 0.99/1.07  
% 0.99/1.07  --bmc1_incremental                      false
% 0.99/1.07  --bmc1_axioms                           reachable_all
% 0.99/1.07  --bmc1_min_bound                        0
% 0.99/1.07  --bmc1_max_bound                        -1
% 0.99/1.07  --bmc1_max_bound_default                -1
% 0.99/1.07  --bmc1_symbol_reachability              true
% 0.99/1.07  --bmc1_property_lemmas                  false
% 0.99/1.07  --bmc1_k_induction                      false
% 0.99/1.07  --bmc1_non_equiv_states                 false
% 0.99/1.07  --bmc1_deadlock                         false
% 0.99/1.07  --bmc1_ucm                              false
% 0.99/1.07  --bmc1_add_unsat_core                   none
% 0.99/1.07  --bmc1_unsat_core_children              false
% 0.99/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.07  --bmc1_out_stat                         full
% 0.99/1.07  --bmc1_ground_init                      false
% 0.99/1.07  --bmc1_pre_inst_next_state              false
% 0.99/1.07  --bmc1_pre_inst_state                   false
% 0.99/1.07  --bmc1_pre_inst_reach_state             false
% 0.99/1.07  --bmc1_out_unsat_core                   false
% 0.99/1.07  --bmc1_aig_witness_out                  false
% 0.99/1.07  --bmc1_verbose                          false
% 0.99/1.07  --bmc1_dump_clauses_tptp                false
% 0.99/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.07  --bmc1_dump_file                        -
% 0.99/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.07  --bmc1_ucm_extend_mode                  1
% 0.99/1.07  --bmc1_ucm_init_mode                    2
% 0.99/1.07  --bmc1_ucm_cone_mode                    none
% 0.99/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.07  --bmc1_ucm_relax_model                  4
% 0.99/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.07  --bmc1_ucm_layered_model                none
% 0.99/1.07  --bmc1_ucm_max_lemma_size               10
% 0.99/1.07  
% 0.99/1.07  ------ AIG Options
% 0.99/1.07  
% 0.99/1.07  --aig_mode                              false
% 0.99/1.07  
% 0.99/1.07  ------ Instantiation Options
% 0.99/1.07  
% 0.99/1.07  --instantiation_flag                    true
% 0.99/1.07  --inst_sos_flag                         false
% 0.99/1.07  --inst_sos_phase                        true
% 0.99/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.07  --inst_lit_sel_side                     num_symb
% 0.99/1.07  --inst_solver_per_active                1400
% 0.99/1.07  --inst_solver_calls_frac                1.
% 0.99/1.07  --inst_passive_queue_type               priority_queues
% 0.99/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.07  --inst_passive_queues_freq              [25;2]
% 0.99/1.07  --inst_dismatching                      true
% 0.99/1.07  --inst_eager_unprocessed_to_passive     true
% 0.99/1.07  --inst_prop_sim_given                   true
% 0.99/1.07  --inst_prop_sim_new                     false
% 0.99/1.07  --inst_subs_new                         false
% 0.99/1.07  --inst_eq_res_simp                      false
% 0.99/1.07  --inst_subs_given                       false
% 0.99/1.07  --inst_orphan_elimination               true
% 0.99/1.07  --inst_learning_loop_flag               true
% 0.99/1.07  --inst_learning_start                   3000
% 0.99/1.07  --inst_learning_factor                  2
% 0.99/1.07  --inst_start_prop_sim_after_learn       3
% 0.99/1.07  --inst_sel_renew                        solver
% 0.99/1.07  --inst_lit_activity_flag                true
% 0.99/1.07  --inst_restr_to_given                   false
% 0.99/1.07  --inst_activity_threshold               500
% 0.99/1.07  --inst_out_proof                        true
% 0.99/1.07  
% 0.99/1.07  ------ Resolution Options
% 0.99/1.07  
% 0.99/1.07  --resolution_flag                       true
% 0.99/1.07  --res_lit_sel                           adaptive
% 0.99/1.07  --res_lit_sel_side                      none
% 0.99/1.07  --res_ordering                          kbo
% 0.99/1.07  --res_to_prop_solver                    active
% 0.99/1.07  --res_prop_simpl_new                    false
% 0.99/1.07  --res_prop_simpl_given                  true
% 0.99/1.07  --res_passive_queue_type                priority_queues
% 0.99/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.07  --res_passive_queues_freq               [15;5]
% 0.99/1.07  --res_forward_subs                      full
% 0.99/1.07  --res_backward_subs                     full
% 0.99/1.07  --res_forward_subs_resolution           true
% 0.99/1.07  --res_backward_subs_resolution          true
% 0.99/1.07  --res_orphan_elimination                true
% 0.99/1.07  --res_time_limit                        2.
% 0.99/1.07  --res_out_proof                         true
% 0.99/1.07  
% 0.99/1.07  ------ Superposition Options
% 0.99/1.07  
% 0.99/1.07  --superposition_flag                    true
% 0.99/1.07  --sup_passive_queue_type                priority_queues
% 0.99/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.07  --demod_completeness_check              fast
% 0.99/1.07  --demod_use_ground                      true
% 0.99/1.07  --sup_to_prop_solver                    passive
% 0.99/1.07  --sup_prop_simpl_new                    true
% 0.99/1.07  --sup_prop_simpl_given                  true
% 0.99/1.07  --sup_fun_splitting                     false
% 0.99/1.07  --sup_smt_interval                      50000
% 0.99/1.07  
% 0.99/1.07  ------ Superposition Simplification Setup
% 0.99/1.07  
% 0.99/1.07  --sup_indices_passive                   []
% 0.99/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.07  --sup_full_bw                           [BwDemod]
% 0.99/1.07  --sup_immed_triv                        [TrivRules]
% 0.99/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.07  --sup_immed_bw_main                     []
% 0.99/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.07  
% 0.99/1.07  ------ Combination Options
% 0.99/1.07  
% 0.99/1.07  --comb_res_mult                         3
% 0.99/1.07  --comb_sup_mult                         2
% 0.99/1.07  --comb_inst_mult                        10
% 0.99/1.07  
% 0.99/1.07  ------ Debug Options
% 0.99/1.07  
% 0.99/1.07  --dbg_backtrace                         false
% 0.99/1.07  --dbg_dump_prop_clauses                 false
% 0.99/1.07  --dbg_dump_prop_clauses_file            -
% 0.99/1.07  --dbg_out_stat                          false
% 0.99/1.07  ------ Parsing...
% 0.99/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/1.07  
% 0.99/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 0.99/1.07  
% 0.99/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/1.07  
% 0.99/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.99/1.07  ------ Proving...
% 0.99/1.07  ------ Problem Properties 
% 0.99/1.07  
% 0.99/1.07  
% 0.99/1.07  clauses                                 14
% 0.99/1.07  conjectures                             3
% 0.99/1.07  EPR                                     2
% 0.99/1.07  Horn                                    12
% 0.99/1.07  unary                                   9
% 0.99/1.07  binary                                  2
% 0.99/1.07  lits                                    32
% 0.99/1.07  lits eq                                 9
% 0.99/1.07  fd_pure                                 0
% 0.99/1.07  fd_pseudo                               0
% 0.99/1.07  fd_cond                                 0
% 0.99/1.07  fd_pseudo_cond                          0
% 0.99/1.07  AC symbols                              0
% 0.99/1.07  
% 0.99/1.07  ------ Schedule dynamic 5 is on 
% 0.99/1.07  
% 0.99/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/1.07  
% 0.99/1.07  
% 0.99/1.07  ------ 
% 0.99/1.07  Current options:
% 0.99/1.07  ------ 
% 0.99/1.07  
% 0.99/1.07  ------ Input Options
% 0.99/1.07  
% 0.99/1.07  --out_options                           all
% 0.99/1.07  --tptp_safe_out                         true
% 0.99/1.07  --problem_path                          ""
% 0.99/1.07  --include_path                          ""
% 0.99/1.07  --clausifier                            res/vclausify_rel
% 0.99/1.07  --clausifier_options                    --mode clausify
% 0.99/1.07  --stdin                                 false
% 0.99/1.07  --stats_out                             all
% 0.99/1.07  
% 0.99/1.07  ------ General Options
% 0.99/1.07  
% 0.99/1.07  --fof                                   false
% 0.99/1.07  --time_out_real                         305.
% 0.99/1.07  --time_out_virtual                      -1.
% 0.99/1.07  --symbol_type_check                     false
% 0.99/1.07  --clausify_out                          false
% 0.99/1.07  --sig_cnt_out                           false
% 0.99/1.07  --trig_cnt_out                          false
% 0.99/1.07  --trig_cnt_out_tolerance                1.
% 0.99/1.07  --trig_cnt_out_sk_spl                   false
% 0.99/1.07  --abstr_cl_out                          false
% 0.99/1.07  
% 0.99/1.07  ------ Global Options
% 0.99/1.07  
% 0.99/1.07  --schedule                              default
% 0.99/1.07  --add_important_lit                     false
% 0.99/1.07  --prop_solver_per_cl                    1000
% 0.99/1.07  --min_unsat_core                        false
% 0.99/1.07  --soft_assumptions                      false
% 0.99/1.07  --soft_lemma_size                       3
% 0.99/1.07  --prop_impl_unit_size                   0
% 0.99/1.07  --prop_impl_unit                        []
% 0.99/1.07  --share_sel_clauses                     true
% 0.99/1.07  --reset_solvers                         false
% 0.99/1.07  --bc_imp_inh                            [conj_cone]
% 0.99/1.07  --conj_cone_tolerance                   3.
% 0.99/1.07  --extra_neg_conj                        none
% 0.99/1.07  --large_theory_mode                     true
% 0.99/1.07  --prolific_symb_bound                   200
% 0.99/1.07  --lt_threshold                          2000
% 0.99/1.07  --clause_weak_htbl                      true
% 0.99/1.07  --gc_record_bc_elim                     false
% 0.99/1.07  
% 0.99/1.07  ------ Preprocessing Options
% 0.99/1.07  
% 0.99/1.07  --preprocessing_flag                    true
% 0.99/1.07  --time_out_prep_mult                    0.1
% 0.99/1.07  --splitting_mode                        input
% 0.99/1.07  --splitting_grd                         true
% 0.99/1.07  --splitting_cvd                         false
% 0.99/1.07  --splitting_cvd_svl                     false
% 0.99/1.07  --splitting_nvd                         32
% 0.99/1.07  --sub_typing                            true
% 0.99/1.07  --prep_gs_sim                           true
% 0.99/1.07  --prep_unflatten                        true
% 0.99/1.07  --prep_res_sim                          true
% 0.99/1.07  --prep_upred                            true
% 0.99/1.07  --prep_sem_filter                       exhaustive
% 0.99/1.07  --prep_sem_filter_out                   false
% 0.99/1.07  --pred_elim                             true
% 0.99/1.07  --res_sim_input                         true
% 0.99/1.07  --eq_ax_congr_red                       true
% 0.99/1.07  --pure_diseq_elim                       true
% 0.99/1.07  --brand_transform                       false
% 0.99/1.07  --non_eq_to_eq                          false
% 0.99/1.07  --prep_def_merge                        true
% 0.99/1.07  --prep_def_merge_prop_impl              false
% 0.99/1.07  --prep_def_merge_mbd                    true
% 0.99/1.07  --prep_def_merge_tr_red                 false
% 0.99/1.07  --prep_def_merge_tr_cl                  false
% 0.99/1.07  --smt_preprocessing                     true
% 0.99/1.07  --smt_ac_axioms                         fast
% 0.99/1.07  --preprocessed_out                      false
% 0.99/1.07  --preprocessed_stats                    false
% 0.99/1.07  
% 0.99/1.07  ------ Abstraction refinement Options
% 0.99/1.07  
% 0.99/1.07  --abstr_ref                             []
% 0.99/1.07  --abstr_ref_prep                        false
% 0.99/1.07  --abstr_ref_until_sat                   false
% 0.99/1.07  --abstr_ref_sig_restrict                funpre
% 0.99/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.07  --abstr_ref_under                       []
% 0.99/1.07  
% 0.99/1.07  ------ SAT Options
% 0.99/1.07  
% 0.99/1.07  --sat_mode                              false
% 0.99/1.07  --sat_fm_restart_options                ""
% 0.99/1.07  --sat_gr_def                            false
% 0.99/1.07  --sat_epr_types                         true
% 0.99/1.07  --sat_non_cyclic_types                  false
% 0.99/1.07  --sat_finite_models                     false
% 0.99/1.07  --sat_fm_lemmas                         false
% 0.99/1.07  --sat_fm_prep                           false
% 0.99/1.07  --sat_fm_uc_incr                        true
% 0.99/1.07  --sat_out_model                         small
% 0.99/1.07  --sat_out_clauses                       false
% 0.99/1.07  
% 0.99/1.07  ------ QBF Options
% 0.99/1.07  
% 0.99/1.07  --qbf_mode                              false
% 0.99/1.07  --qbf_elim_univ                         false
% 0.99/1.07  --qbf_dom_inst                          none
% 0.99/1.07  --qbf_dom_pre_inst                      false
% 0.99/1.07  --qbf_sk_in                             false
% 0.99/1.07  --qbf_pred_elim                         true
% 0.99/1.07  --qbf_split                             512
% 0.99/1.07  
% 0.99/1.07  ------ BMC1 Options
% 0.99/1.07  
% 0.99/1.07  --bmc1_incremental                      false
% 0.99/1.07  --bmc1_axioms                           reachable_all
% 0.99/1.07  --bmc1_min_bound                        0
% 0.99/1.07  --bmc1_max_bound                        -1
% 0.99/1.07  --bmc1_max_bound_default                -1
% 0.99/1.07  --bmc1_symbol_reachability              true
% 0.99/1.07  --bmc1_property_lemmas                  false
% 0.99/1.07  --bmc1_k_induction                      false
% 0.99/1.07  --bmc1_non_equiv_states                 false
% 0.99/1.07  --bmc1_deadlock                         false
% 0.99/1.07  --bmc1_ucm                              false
% 0.99/1.07  --bmc1_add_unsat_core                   none
% 0.99/1.07  --bmc1_unsat_core_children              false
% 0.99/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.07  --bmc1_out_stat                         full
% 0.99/1.07  --bmc1_ground_init                      false
% 0.99/1.07  --bmc1_pre_inst_next_state              false
% 0.99/1.07  --bmc1_pre_inst_state                   false
% 0.99/1.07  --bmc1_pre_inst_reach_state             false
% 0.99/1.07  --bmc1_out_unsat_core                   false
% 0.99/1.07  --bmc1_aig_witness_out                  false
% 0.99/1.07  --bmc1_verbose                          false
% 0.99/1.07  --bmc1_dump_clauses_tptp                false
% 0.99/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.07  --bmc1_dump_file                        -
% 0.99/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.07  --bmc1_ucm_extend_mode                  1
% 0.99/1.07  --bmc1_ucm_init_mode                    2
% 0.99/1.07  --bmc1_ucm_cone_mode                    none
% 0.99/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.07  --bmc1_ucm_relax_model                  4
% 0.99/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.07  --bmc1_ucm_layered_model                none
% 0.99/1.07  --bmc1_ucm_max_lemma_size               10
% 0.99/1.07  
% 0.99/1.07  ------ AIG Options
% 0.99/1.07  
% 0.99/1.07  --aig_mode                              false
% 0.99/1.07  
% 0.99/1.07  ------ Instantiation Options
% 0.99/1.07  
% 0.99/1.07  --instantiation_flag                    true
% 0.99/1.07  --inst_sos_flag                         false
% 0.99/1.07  --inst_sos_phase                        true
% 0.99/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.07  --inst_lit_sel_side                     none
% 0.99/1.07  --inst_solver_per_active                1400
% 0.99/1.07  --inst_solver_calls_frac                1.
% 0.99/1.07  --inst_passive_queue_type               priority_queues
% 0.99/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.07  --inst_passive_queues_freq              [25;2]
% 0.99/1.07  --inst_dismatching                      true
% 0.99/1.07  --inst_eager_unprocessed_to_passive     true
% 0.99/1.07  --inst_prop_sim_given                   true
% 0.99/1.07  --inst_prop_sim_new                     false
% 0.99/1.07  --inst_subs_new                         false
% 0.99/1.07  --inst_eq_res_simp                      false
% 0.99/1.07  --inst_subs_given                       false
% 0.99/1.07  --inst_orphan_elimination               true
% 0.99/1.07  --inst_learning_loop_flag               true
% 0.99/1.07  --inst_learning_start                   3000
% 0.99/1.07  --inst_learning_factor                  2
% 0.99/1.07  --inst_start_prop_sim_after_learn       3
% 0.99/1.07  --inst_sel_renew                        solver
% 0.99/1.07  --inst_lit_activity_flag                true
% 0.99/1.07  --inst_restr_to_given                   false
% 0.99/1.07  --inst_activity_threshold               500
% 0.99/1.07  --inst_out_proof                        true
% 0.99/1.07  
% 0.99/1.07  ------ Resolution Options
% 0.99/1.07  
% 0.99/1.07  --resolution_flag                       false
% 0.99/1.07  --res_lit_sel                           adaptive
% 0.99/1.07  --res_lit_sel_side                      none
% 0.99/1.07  --res_ordering                          kbo
% 0.99/1.07  --res_to_prop_solver                    active
% 0.99/1.07  --res_prop_simpl_new                    false
% 0.99/1.07  --res_prop_simpl_given                  true
% 0.99/1.07  --res_passive_queue_type                priority_queues
% 0.99/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.07  --res_passive_queues_freq               [15;5]
% 0.99/1.07  --res_forward_subs                      full
% 0.99/1.07  --res_backward_subs                     full
% 0.99/1.07  --res_forward_subs_resolution           true
% 0.99/1.07  --res_backward_subs_resolution          true
% 0.99/1.07  --res_orphan_elimination                true
% 0.99/1.07  --res_time_limit                        2.
% 0.99/1.07  --res_out_proof                         true
% 0.99/1.07  
% 0.99/1.07  ------ Superposition Options
% 0.99/1.07  
% 0.99/1.07  --superposition_flag                    true
% 0.99/1.07  --sup_passive_queue_type                priority_queues
% 0.99/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.07  --demod_completeness_check              fast
% 0.99/1.07  --demod_use_ground                      true
% 0.99/1.07  --sup_to_prop_solver                    passive
% 0.99/1.07  --sup_prop_simpl_new                    true
% 0.99/1.07  --sup_prop_simpl_given                  true
% 0.99/1.07  --sup_fun_splitting                     false
% 0.99/1.07  --sup_smt_interval                      50000
% 0.99/1.07  
% 0.99/1.07  ------ Superposition Simplification Setup
% 0.99/1.07  
% 0.99/1.07  --sup_indices_passive                   []
% 0.99/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.07  --sup_full_bw                           [BwDemod]
% 0.99/1.07  --sup_immed_triv                        [TrivRules]
% 0.99/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.07  --sup_immed_bw_main                     []
% 0.99/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.07  
% 0.99/1.07  ------ Combination Options
% 0.99/1.07  
% 0.99/1.07  --comb_res_mult                         3
% 0.99/1.07  --comb_sup_mult                         2
% 0.99/1.07  --comb_inst_mult                        10
% 0.99/1.07  
% 0.99/1.07  ------ Debug Options
% 0.99/1.07  
% 0.99/1.07  --dbg_backtrace                         false
% 0.99/1.07  --dbg_dump_prop_clauses                 false
% 0.99/1.07  --dbg_dump_prop_clauses_file            -
% 0.99/1.07  --dbg_out_stat                          false
% 0.99/1.07  
% 0.99/1.07  
% 0.99/1.07  
% 0.99/1.07  
% 0.99/1.07  ------ Proving...
% 0.99/1.07  
% 0.99/1.07  
% 0.99/1.07  % SZS status Theorem for theBenchmark.p
% 0.99/1.07  
% 0.99/1.07   Resolution empty clause
% 0.99/1.07  
% 0.99/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/1.07  
% 0.99/1.07  fof(f14,conjecture,(
% 0.99/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f15,negated_conjecture,(
% 0.99/1.07    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.99/1.07    inference(negated_conjecture,[],[f14])).
% 0.99/1.07  
% 0.99/1.07  fof(f36,plain,(
% 0.99/1.07    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.99/1.07    inference(ennf_transformation,[],[f15])).
% 0.99/1.07  
% 0.99/1.07  fof(f37,plain,(
% 0.99/1.07    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f36])).
% 0.99/1.07  
% 0.99/1.07  fof(f45,plain,(
% 0.99/1.07    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.99/1.07    inference(nnf_transformation,[],[f37])).
% 0.99/1.07  
% 0.99/1.07  fof(f46,plain,(
% 0.99/1.07    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f45])).
% 0.99/1.07  
% 0.99/1.07  fof(f49,plain,(
% 0.99/1.07    ( ! [X0,X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_waybel_7(X0,X1,sK4) | ~r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,sK4) | r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 0.99/1.07    introduced(choice_axiom,[])).
% 0.99/1.07  
% 0.99/1.07  fof(f48,plain,(
% 0.99/1.07    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(X0,sK3,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)))) & (r2_waybel_7(X0,sK3,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK3))) )),
% 0.99/1.07    introduced(choice_axiom,[])).
% 0.99/1.07  
% 0.99/1.07  fof(f47,plain,(
% 0.99/1.07    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK2,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)))) & (r2_waybel_7(sK2,X1,X2) | r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.99/1.07    introduced(choice_axiom,[])).
% 0.99/1.07  
% 0.99/1.07  fof(f50,plain,(
% 0.99/1.07    (((~r2_waybel_7(sK2,sK3,sK4) | ~r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))) & (r2_waybel_7(sK2,sK3,sK4) | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.99/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f49,f48,f47])).
% 0.99/1.07  
% 0.99/1.07  fof(f75,plain,(
% 0.99/1.07    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f8,axiom,(
% 0.99/1.07    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f60,plain,(
% 0.99/1.07    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.99/1.07    inference(cnf_transformation,[],[f8])).
% 0.99/1.07  
% 0.99/1.07  fof(f90,plain,(
% 0.99/1.07    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 0.99/1.07    inference(definition_unfolding,[],[f75,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f76,plain,(
% 0.99/1.07    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f89,plain,(
% 0.99/1.07    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 0.99/1.07    inference(definition_unfolding,[],[f76,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f11,axiom,(
% 0.99/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f17,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.99/1.07    inference(pure_predicate_removal,[],[f11])).
% 0.99/1.07  
% 0.99/1.07  fof(f30,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.99/1.07    inference(ennf_transformation,[],[f17])).
% 0.99/1.07  
% 0.99/1.07  fof(f31,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f30])).
% 0.99/1.07  
% 0.99/1.07  fof(f66,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f31])).
% 0.99/1.07  
% 0.99/1.07  fof(f85,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(definition_unfolding,[],[f66,f60,f60,f60,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f74,plain,(
% 0.99/1.07    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f91,plain,(
% 0.99/1.07    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))),
% 0.99/1.07    inference(definition_unfolding,[],[f74,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f73,plain,(
% 0.99/1.07    ~v1_xboole_0(sK3)),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f6,axiom,(
% 0.99/1.07    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f23,plain,(
% 0.99/1.07    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.99/1.07    inference(ennf_transformation,[],[f6])).
% 0.99/1.07  
% 0.99/1.07  fof(f57,plain,(
% 0.99/1.07    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f23])).
% 0.99/1.07  
% 0.99/1.07  fof(f72,plain,(
% 0.99/1.07    l1_pre_topc(sK2)),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f70,plain,(
% 0.99/1.07    ~v2_struct_0(sK2)),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f9,axiom,(
% 0.99/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f18,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.99/1.07    inference(pure_predicate_removal,[],[f9])).
% 0.99/1.07  
% 0.99/1.07  fof(f26,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.99/1.07    inference(ennf_transformation,[],[f18])).
% 0.99/1.07  
% 0.99/1.07  fof(f27,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f26])).
% 0.99/1.07  
% 0.99/1.07  fof(f61,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f27])).
% 0.99/1.07  
% 0.99/1.07  fof(f82,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(definition_unfolding,[],[f61,f60,f60,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f10,axiom,(
% 0.99/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f16,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.99/1.07    inference(pure_predicate_removal,[],[f10])).
% 0.99/1.07  
% 0.99/1.07  fof(f19,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.99/1.07    inference(pure_predicate_removal,[],[f16])).
% 0.99/1.07  
% 0.99/1.07  fof(f28,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.99/1.07    inference(ennf_transformation,[],[f19])).
% 0.99/1.07  
% 0.99/1.07  fof(f29,plain,(
% 0.99/1.07    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f28])).
% 0.99/1.07  
% 0.99/1.07  fof(f64,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f29])).
% 0.99/1.07  
% 0.99/1.07  fof(f83,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(definition_unfolding,[],[f64,f60,f60,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f80,plain,(
% 0.99/1.07    ~r2_waybel_7(sK2,sK3,sK4) | ~r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f12,axiom,(
% 0.99/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f32,plain,(
% 0.99/1.07    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/1.07    inference(ennf_transformation,[],[f12])).
% 0.99/1.07  
% 0.99/1.07  fof(f33,plain,(
% 0.99/1.07    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f32])).
% 0.99/1.07  
% 0.99/1.07  fof(f44,plain,(
% 0.99/1.07    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(nnf_transformation,[],[f33])).
% 0.99/1.07  
% 0.99/1.07  fof(f67,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f44])).
% 0.99/1.07  
% 0.99/1.07  fof(f71,plain,(
% 0.99/1.07    v2_pre_topc(sK2)),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f78,plain,(
% 0.99/1.07    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f62,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f27])).
% 0.99/1.07  
% 0.99/1.07  fof(f81,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(definition_unfolding,[],[f62,f60,f60,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f5,axiom,(
% 0.99/1.07    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f22,plain,(
% 0.99/1.07    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.99/1.07    inference(ennf_transformation,[],[f5])).
% 0.99/1.07  
% 0.99/1.07  fof(f56,plain,(
% 0.99/1.07    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f22])).
% 0.99/1.07  
% 0.99/1.07  fof(f13,axiom,(
% 0.99/1.07    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f34,plain,(
% 0.99/1.07    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.99/1.07    inference(ennf_transformation,[],[f13])).
% 0.99/1.07  
% 0.99/1.07  fof(f35,plain,(
% 0.99/1.07    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f34])).
% 0.99/1.07  
% 0.99/1.07  fof(f69,plain,(
% 0.99/1.07    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f35])).
% 0.99/1.07  
% 0.99/1.07  fof(f87,plain,(
% 0.99/1.07    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(definition_unfolding,[],[f69,f60,f60,f60,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f77,plain,(
% 0.99/1.07    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f88,plain,(
% 0.99/1.07    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))),
% 0.99/1.07    inference(definition_unfolding,[],[f77,f60])).
% 0.99/1.07  
% 0.99/1.07  fof(f7,axiom,(
% 0.99/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f20,plain,(
% 0.99/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.99/1.07    inference(pure_predicate_removal,[],[f7])).
% 0.99/1.07  
% 0.99/1.07  fof(f24,plain,(
% 0.99/1.07    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/1.07    inference(ennf_transformation,[],[f20])).
% 0.99/1.07  
% 0.99/1.07  fof(f25,plain,(
% 0.99/1.07    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(flattening,[],[f24])).
% 0.99/1.07  
% 0.99/1.07  fof(f42,plain,(
% 0.99/1.07    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.99/1.07    introduced(choice_axiom,[])).
% 0.99/1.07  
% 0.99/1.07  fof(f43,plain,(
% 0.99/1.07    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f42])).
% 0.99/1.07  
% 0.99/1.07  fof(f59,plain,(
% 0.99/1.07    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f43])).
% 0.99/1.07  
% 0.99/1.07  fof(f79,plain,(
% 0.99/1.07    r2_waybel_7(sK2,sK3,sK4) | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))),
% 0.99/1.07    inference(cnf_transformation,[],[f50])).
% 0.99/1.07  
% 0.99/1.07  fof(f68,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f44])).
% 0.99/1.07  
% 0.99/1.07  fof(f1,axiom,(
% 0.99/1.07    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f38,plain,(
% 0.99/1.07    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.99/1.07    inference(nnf_transformation,[],[f1])).
% 0.99/1.07  
% 0.99/1.07  fof(f39,plain,(
% 0.99/1.07    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.99/1.07    inference(rectify,[],[f38])).
% 0.99/1.07  
% 0.99/1.07  fof(f40,plain,(
% 0.99/1.07    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.99/1.07    introduced(choice_axiom,[])).
% 0.99/1.07  
% 0.99/1.07  fof(f41,plain,(
% 0.99/1.07    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.99/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 0.99/1.07  
% 0.99/1.07  fof(f52,plain,(
% 0.99/1.07    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f41])).
% 0.99/1.07  
% 0.99/1.07  fof(f58,plain,(
% 0.99/1.07    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f43])).
% 0.99/1.07  
% 0.99/1.07  fof(f4,axiom,(
% 0.99/1.07    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f21,plain,(
% 0.99/1.07    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.99/1.07    inference(ennf_transformation,[],[f4])).
% 0.99/1.07  
% 0.99/1.07  fof(f55,plain,(
% 0.99/1.07    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.99/1.07    inference(cnf_transformation,[],[f21])).
% 0.99/1.07  
% 0.99/1.07  fof(f3,axiom,(
% 0.99/1.07    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f54,plain,(
% 0.99/1.07    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.99/1.07    inference(cnf_transformation,[],[f3])).
% 0.99/1.07  
% 0.99/1.07  fof(f2,axiom,(
% 0.99/1.07    ! [X0] : k2_subset_1(X0) = X0),
% 0.99/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.07  
% 0.99/1.07  fof(f53,plain,(
% 0.99/1.07    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.99/1.07    inference(cnf_transformation,[],[f2])).
% 0.99/1.07  
% 0.99/1.07  cnf(c_23,negated_conjecture,
% 0.99/1.07      ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 0.99/1.07      inference(cnf_transformation,[],[f90]) ).
% 0.99/1.07  
% 0.99/1.07  cnf(c_22,negated_conjecture,
% 0.99/1.07      ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 0.99/1.07      inference(cnf_transformation,[],[f89]) ).
% 0.99/1.07  
% 0.99/1.07  cnf(c_13,plain,
% 0.99/1.07      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 0.99/1.07      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.07      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 0.99/1.07      | v2_struct_0(X2)
% 0.99/1.07      | ~ l1_struct_0(X2)
% 0.99/1.07      | v1_xboole_0(X0)
% 0.99/1.07      | v1_xboole_0(X1) ),
% 0.99/1.07      inference(cnf_transformation,[],[f85]) ).
% 0.99/1.07  
% 0.99/1.07  cnf(c_24,negated_conjecture,
% 0.99/1.07      ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
% 0.99/1.07      inference(cnf_transformation,[],[f91]) ).
% 0.99/1.07  
% 0.99/1.07  cnf(c_374,plain,
% 0.99/1.07      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.07      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 0.99/1.07      | v2_struct_0(X2)
% 0.99/1.07      | ~ l1_struct_0(X2)
% 0.99/1.07      | v1_xboole_0(X0)
% 0.99/1.07      | v1_xboole_0(X1)
% 0.99/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 0.99/1.07      | sK3 != X0 ),
% 0.99/1.07      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 0.99/1.07  
% 0.99/1.07  cnf(c_375,plain,
% 0.99/1.07      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.07      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.07      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.07      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.07      | v2_struct_0(X1)
% 0.99/1.07      | ~ l1_struct_0(X1)
% 0.99/1.07      | v1_xboole_0(X0)
% 0.99/1.07      | v1_xboole_0(sK3)
% 0.99/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_374]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_25,negated_conjecture,
% 0.99/1.08      ( ~ v1_xboole_0(sK3) ),
% 0.99/1.08      inference(cnf_transformation,[],[f73]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_379,plain,
% 0.99/1.08      ( v1_xboole_0(X0)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_375,c_25]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_380,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 0.99/1.08      inference(renaming,[status(thm)],[c_379]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1359,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | sK3 != sK3 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_22,c_380]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1752,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | sK3 != sK3 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_23,c_1359]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_6,plain,
% 0.99/1.08      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 0.99/1.08      inference(cnf_transformation,[],[f57]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_26,negated_conjecture,
% 0.99/1.08      ( l1_pre_topc(sK2) ),
% 0.99/1.08      inference(cnf_transformation,[],[f72]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_572,plain,
% 0.99/1.08      ( l1_struct_0(X0) | sK2 != X0 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_6,c_26]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_573,plain,
% 0.99/1.08      ( l1_struct_0(sK2) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_572]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2118,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | sK3 != sK3
% 0.99/1.08      | sK2 != X1 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_1752,c_573]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2119,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | v2_struct_0(sK2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_2118]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_28,negated_conjecture,
% 0.99/1.08      ( ~ v2_struct_0(sK2) ),
% 0.99/1.08      inference(cnf_transformation,[],[f70]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2123,plain,
% 0.99/1.08      ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_2119,c_28]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2124,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 0.99/1.08      inference(renaming,[status(thm)],[c_2123]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_10,plain,
% 0.99/1.08      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.08      | v2_struct_0(X2)
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 0.99/1.08      | ~ l1_struct_0(X2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(X1) ),
% 0.99/1.08      inference(cnf_transformation,[],[f82]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1287,plain,
% 0.99/1.08      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.08      | v2_struct_0(X2)
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 0.99/1.08      | ~ l1_struct_0(X2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(X1)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 0.99/1.08      | sK3 != X0 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1288,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(sK3)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_1287]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1292,plain,
% 0.99/1.08      ( v1_xboole_0(X0)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_1288,c_25]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1293,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(renaming,[status(thm)],[c_1292]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1813,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | sK3 != sK3 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_23,c_1293]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2091,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | sK3 != sK3
% 0.99/1.08      | sK2 != X1 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_1813,c_573]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2092,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | v2_struct_0(sK2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_2091]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2096,plain,
% 0.99/1.08      ( ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_2092,c_28]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2097,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(renaming,[status(thm)],[c_2096]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_11,plain,
% 0.99/1.08      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 0.99/1.08      | v2_struct_0(X2)
% 0.99/1.08      | ~ l1_struct_0(X2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(X1) ),
% 0.99/1.08      inference(cnf_transformation,[],[f83]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1251,plain,
% 0.99/1.08      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 0.99/1.08      | v2_struct_0(X2)
% 0.99/1.08      | ~ l1_struct_0(X2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(X1)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 0.99/1.08      | sK3 != X0 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1252,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(sK3)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_1251]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1256,plain,
% 0.99/1.08      ( v1_xboole_0(X0)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_1252,c_25]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1257,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(renaming,[status(thm)],[c_1256]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1842,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | sK3 != sK3 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_23,c_1257]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2064,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 0.99/1.08      | sK3 != sK3
% 0.99/1.08      | sK2 != X1 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_1842,c_573]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2065,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | v2_struct_0(sK2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_2064]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2069,plain,
% 0.99/1.08      ( v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_2065,c_28]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_2070,plain,
% 0.99/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(renaming,[status(thm)],[c_2069]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_18,negated_conjecture,
% 0.99/1.08      ( ~ r2_waybel_7(sK2,sK3,sK4)
% 0.99/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 0.99/1.08      inference(cnf_transformation,[],[f80]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_210,plain,
% 0.99/1.08      ( ~ r2_waybel_7(sK2,sK3,sK4)
% 0.99/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 0.99/1.08      inference(prop_impl,[status(thm)],[c_18]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_16,plain,
% 0.99/1.08      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 0.99/1.08      | ~ l1_waybel_0(X1,X0)
% 0.99/1.08      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.99/1.08      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 0.99/1.08      | ~ v7_waybel_0(X1)
% 0.99/1.08      | ~ v4_orders_2(X1)
% 0.99/1.08      | v2_struct_0(X0)
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ v2_pre_topc(X0)
% 0.99/1.08      | ~ l1_pre_topc(X0) ),
% 0.99/1.08      inference(cnf_transformation,[],[f67]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_27,negated_conjecture,
% 0.99/1.08      ( v2_pre_topc(sK2) ),
% 0.99/1.08      inference(cnf_transformation,[],[f71]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_464,plain,
% 0.99/1.08      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 0.99/1.08      | ~ l1_waybel_0(X1,X0)
% 0.99/1.08      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.99/1.08      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 0.99/1.08      | ~ v7_waybel_0(X1)
% 0.99/1.08      | ~ v4_orders_2(X1)
% 0.99/1.08      | v2_struct_0(X0)
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_pre_topc(X0)
% 0.99/1.08      | sK2 != X0 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_465,plain,
% 0.99/1.08      ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 0.99/1.08      | ~ l1_waybel_0(X0,sK2)
% 0.99/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.99/1.08      | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
% 0.99/1.08      | ~ v7_waybel_0(X0)
% 0.99/1.08      | ~ v4_orders_2(X0)
% 0.99/1.08      | v2_struct_0(X0)
% 0.99/1.08      | v2_struct_0(sK2)
% 0.99/1.08      | ~ l1_pre_topc(sK2) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_464]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_469,plain,
% 0.99/1.08      ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 0.99/1.08      | ~ l1_waybel_0(X0,sK2)
% 0.99/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.99/1.08      | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
% 0.99/1.08      | ~ v7_waybel_0(X0)
% 0.99/1.08      | ~ v4_orders_2(X0)
% 0.99/1.08      | v2_struct_0(X0) ),
% 0.99/1.08      inference(global_propositional_subsumption,
% 0.99/1.08                [status(thm)],
% 0.99/1.08                [c_465,c_28,c_26]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_908,plain,
% 0.99/1.08      ( ~ l1_waybel_0(X0,sK2)
% 0.99/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.99/1.08      | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
% 0.99/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 0.99/1.08      | ~ v7_waybel_0(X0)
% 0.99/1.08      | ~ v4_orders_2(X0)
% 0.99/1.08      | v2_struct_0(X0)
% 0.99/1.08      | k2_yellow19(sK2,X0) != sK3
% 0.99/1.08      | sK4 != X1
% 0.99/1.08      | sK2 != sK2 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_210,c_469]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_909,plain,
% 0.99/1.08      ( ~ l1_waybel_0(X0,sK2)
% 0.99/1.08      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 0.99/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 0.99/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 0.99/1.08      | ~ v7_waybel_0(X0)
% 0.99/1.08      | ~ v4_orders_2(X0)
% 0.99/1.08      | v2_struct_0(X0)
% 0.99/1.08      | k2_yellow19(sK2,X0) != sK3 ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_908]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_20,negated_conjecture,
% 0.99/1.08      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 0.99/1.08      inference(cnf_transformation,[],[f78]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_913,plain,
% 0.99/1.08      ( ~ l1_waybel_0(X0,sK2)
% 0.99/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 0.99/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 0.99/1.08      | ~ v7_waybel_0(X0)
% 0.99/1.08      | ~ v4_orders_2(X0)
% 0.99/1.08      | v2_struct_0(X0)
% 0.99/1.08      | k2_yellow19(sK2,X0) != sK3 ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_909,c_20]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_9,plain,
% 0.99/1.08      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 0.99/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.08      | v2_struct_0(X2)
% 0.99/1.08      | ~ l1_struct_0(X2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(X1) ),
% 0.99/1.08      inference(cnf_transformation,[],[f81]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1323,plain,
% 0.99/1.08      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 0.99/1.08      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 0.99/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.08      | v2_struct_0(X2)
% 0.99/1.08      | ~ l1_struct_0(X2)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(X1)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 0.99/1.08      | sK3 != X0 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1324,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | v1_xboole_0(sK3)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(unflattening,[status(thm)],[c_1323]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1328,plain,
% 0.99/1.08      ( v1_xboole_0(X0)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
% 0.99/1.08      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(global_propositional_subsumption,[status(thm)],[c_1324,c_25]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1329,plain,
% 0.99/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 0.99/1.08      | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
% 0.99/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 0.99/1.08      | v2_struct_0(X1)
% 0.99/1.08      | ~ l1_struct_0(X1)
% 0.99/1.08      | v1_xboole_0(X0)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 0.99/1.08      inference(renaming,[status(thm)],[c_1328]) ).
% 0.99/1.08  
% 0.99/1.08  cnf(c_1784,plain,
% 0.99/1.08      ( l1_waybel_0(k3_yellow19(X0,X1,sK3),X0)
% 0.99/1.08      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.99/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 0.99/1.08      | v2_struct_0(X0)
% 0.99/1.08      | ~ l1_struct_0(X0)
% 0.99/1.08      | v1_xboole_0(X1)
% 0.99/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 0.99/1.08      | sK3 != sK3 ),
% 0.99/1.08      inference(resolution_lifted,[status(thm)],[c_23,c_1329]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1942,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,X2))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(X2)
% 1.45/1.08      | ~ v4_orders_2(X2)
% 1.45/1.08      | v2_struct_0(X2)
% 1.45/1.08      | v2_struct_0(X1)
% 1.45/1.08      | ~ l1_struct_0(X1)
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k3_yellow19(X1,X0,sK3) != X2
% 1.45/1.08      | k2_yellow19(sK2,X2) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | sK3 != sK3
% 1.45/1.08      | sK2 != X1 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_913,c_1784]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1943,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(sK2)
% 1.45/1.08      | ~ l1_struct_0(sK2)
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_1942]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_72,plain,
% 1.45/1.08      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 1.45/1.08      inference(instantiation,[status(thm)],[c_6]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1947,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(global_propositional_subsumption,
% 1.45/1.08                [status(thm)],
% 1.45/1.08                [c_1943,c_28,c_26,c_72]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2154,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(backward_subsumption_resolution,[status(thm)],[c_2070,c_1947]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2169,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(backward_subsumption_resolution,[status(thm)],[c_2097,c_2154]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2186,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.45/1.08      inference(resolution,[status(thm)],[c_2124,c_2169]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3233,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.45/1.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 1.45/1.08      | v1_xboole_0(X0) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_2186]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_5,plain,
% 1.45/1.08      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.45/1.08      inference(cnf_transformation,[],[f56]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2059,plain,
% 1.45/1.08      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_5,c_573]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2060,plain,
% 1.45/1.08      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_2059]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3295,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.45/1.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 1.45/1.08      | v1_xboole_0(X0) = iProver_top ),
% 1.45/1.08      inference(light_normalisation,[status(thm)],[c_3233,c_2060]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3486,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 1.45/1.08      inference(equality_resolution,[status(thm)],[c_3295]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_17,plain,
% 1.45/1.08      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.45/1.08      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.45/1.08      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.45/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.45/1.08      | v2_struct_0(X1)
% 1.45/1.08      | ~ l1_struct_0(X1)
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.45/1.08      inference(cnf_transformation,[],[f87]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_413,plain,
% 1.45/1.08      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.45/1.08      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.45/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.45/1.08      | v2_struct_0(X1)
% 1.45/1.08      | ~ l1_struct_0(X1)
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.45/1.08      | sK3 != X0 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_414,plain,
% 1.45/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.45/1.08      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | ~ l1_struct_0(X0)
% 1.45/1.08      | v1_xboole_0(sK3)
% 1.45/1.08      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_413]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_418,plain,
% 1.45/1.08      ( ~ l1_struct_0(X0)
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.45/1.08      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.45/1.08      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.45/1.08      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.45/1.08      inference(global_propositional_subsumption,[status(thm)],[c_414,c_25]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_419,plain,
% 1.45/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.45/1.08      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | ~ l1_struct_0(X0)
% 1.45/1.08      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.45/1.08      inference(renaming,[status(thm)],[c_418]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1394,plain,
% 1.45/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | ~ l1_struct_0(X0)
% 1.45/1.08      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.45/1.08      | sK3 != sK3 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_22,c_419]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1871,plain,
% 1.45/1.08      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | ~ l1_struct_0(X0)
% 1.45/1.08      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.45/1.08      | sK3 != sK3 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_23,c_1394]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2048,plain,
% 1.45/1.08      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.45/1.08      | sK3 != sK3
% 1.45/1.08      | sK2 != X0 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_1871,c_573]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2049,plain,
% 1.45/1.08      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 1.45/1.08      | v2_struct_0(sK2)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_2048]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_21,negated_conjecture,
% 1.45/1.08      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
% 1.45/1.08      inference(cnf_transformation,[],[f88]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_421,plain,
% 1.45/1.08      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.45/1.08      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 1.45/1.08      | v2_struct_0(sK2)
% 1.45/1.08      | ~ l1_struct_0(sK2)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.45/1.08      inference(instantiation,[status(thm)],[c_419]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2051,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.45/1.08      inference(global_propositional_subsumption,
% 1.45/1.08                [status(thm)],
% 1.45/1.08                [c_2049,c_28,c_26,c_23,c_22,c_21,c_72,c_421]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2611,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
% 1.45/1.08      inference(equality_resolution_simp,[status(thm)],[c_2051]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3487,plain,
% 1.45/1.08      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | sK3 != sK3
% 1.45/1.08      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 1.45/1.08      inference(light_normalisation,[status(thm)],[c_3486,c_2611]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3488,plain,
% 1.45/1.08      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 1.45/1.08      inference(equality_resolution_simp,[status(thm)],[c_3487]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_29,plain,
% 1.45/1.08      ( v2_struct_0(sK2) != iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_30,plain,
% 1.45/1.08      ( v2_pre_topc(sK2) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_31,plain,
% 1.45/1.08      ( l1_pre_topc(sK2) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_36,plain,
% 1.45/1.08      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_7,plain,
% 1.45/1.08      ( v2_struct_0(X0)
% 1.45/1.08      | ~ v2_pre_topc(X0)
% 1.45/1.08      | ~ l1_pre_topc(X0)
% 1.45/1.08      | ~ v1_xboole_0(sK1(X0)) ),
% 1.45/1.08      inference(cnf_transformation,[],[f59]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_68,plain,
% 1.45/1.08      ( v2_struct_0(X0) = iProver_top
% 1.45/1.08      | v2_pre_topc(X0) != iProver_top
% 1.45/1.08      | l1_pre_topc(X0) != iProver_top
% 1.45/1.08      | v1_xboole_0(sK1(X0)) != iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_70,plain,
% 1.45/1.08      ( v2_struct_0(sK2) = iProver_top
% 1.45/1.08      | v2_pre_topc(sK2) != iProver_top
% 1.45/1.08      | l1_pre_topc(sK2) != iProver_top
% 1.45/1.08      | v1_xboole_0(sK1(sK2)) != iProver_top ),
% 1.45/1.08      inference(instantiation,[status(thm)],[c_68]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_19,negated_conjecture,
% 1.45/1.08      ( r2_waybel_7(sK2,sK3,sK4)
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 1.45/1.08      inference(cnf_transformation,[],[f79]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_212,plain,
% 1.45/1.08      ( r2_waybel_7(sK2,sK3,sK4)
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 1.45/1.08      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_15,plain,
% 1.45/1.08      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.45/1.08      | ~ l1_waybel_0(X1,X0)
% 1.45/1.08      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.08      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.45/1.08      | ~ v7_waybel_0(X1)
% 1.45/1.08      | ~ v4_orders_2(X1)
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | v2_struct_0(X1)
% 1.45/1.08      | ~ v2_pre_topc(X0)
% 1.45/1.08      | ~ l1_pre_topc(X0) ),
% 1.45/1.08      inference(cnf_transformation,[],[f68]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_497,plain,
% 1.45/1.08      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.45/1.08      | ~ l1_waybel_0(X1,X0)
% 1.45/1.08      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.08      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.45/1.08      | ~ v7_waybel_0(X1)
% 1.45/1.08      | ~ v4_orders_2(X1)
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | v2_struct_0(X1)
% 1.45/1.08      | ~ l1_pre_topc(X0)
% 1.45/1.08      | sK2 != X0 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_498,plain,
% 1.45/1.08      ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 1.45/1.08      | ~ l1_waybel_0(X0,sK2)
% 1.45/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.45/1.08      | r2_hidden(X1,k10_yellow_6(sK2,X0))
% 1.45/1.08      | ~ v7_waybel_0(X0)
% 1.45/1.08      | ~ v4_orders_2(X0)
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | v2_struct_0(sK2)
% 1.45/1.08      | ~ l1_pre_topc(sK2) ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_497]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_502,plain,
% 1.45/1.08      ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 1.45/1.08      | ~ l1_waybel_0(X0,sK2)
% 1.45/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.45/1.08      | r2_hidden(X1,k10_yellow_6(sK2,X0))
% 1.45/1.08      | ~ v7_waybel_0(X0)
% 1.45/1.08      | ~ v4_orders_2(X0)
% 1.45/1.08      | v2_struct_0(X0) ),
% 1.45/1.08      inference(global_propositional_subsumption,
% 1.45/1.08                [status(thm)],
% 1.45/1.08                [c_498,c_28,c_26]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_875,plain,
% 1.45/1.08      ( ~ l1_waybel_0(X0,sK2)
% 1.45/1.08      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.45/1.08      | r2_hidden(X1,k10_yellow_6(sK2,X0))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(X0)
% 1.45/1.08      | ~ v4_orders_2(X0)
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,X0) != sK3
% 1.45/1.08      | sK4 != X1
% 1.45/1.08      | sK2 != sK2 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_212,c_502]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_876,plain,
% 1.45/1.08      ( ~ l1_waybel_0(X0,sK2)
% 1.45/1.08      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(X0)
% 1.45/1.08      | ~ v4_orders_2(X0)
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,X0) != sK3 ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_875]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_880,plain,
% 1.45/1.08      ( ~ l1_waybel_0(X0,sK2)
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(X0)
% 1.45/1.08      | ~ v4_orders_2(X0)
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,X0) != sK3 ),
% 1.45/1.08      inference(global_propositional_subsumption,[status(thm)],[c_876,c_20]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1984,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,X2))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(X2)
% 1.45/1.08      | ~ v4_orders_2(X2)
% 1.45/1.08      | v2_struct_0(X2)
% 1.45/1.08      | v2_struct_0(X1)
% 1.45/1.08      | ~ l1_struct_0(X1)
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k3_yellow19(X1,X0,sK3) != X2
% 1.45/1.08      | k2_yellow19(sK2,X2) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | sK3 != sK3
% 1.45/1.08      | sK2 != X1 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_880,c_1784]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1985,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(sK2)
% 1.45/1.08      | ~ l1_struct_0(sK2)
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_1984]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_1989,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(global_propositional_subsumption,
% 1.45/1.08                [status(thm)],
% 1.45/1.08                [c_1985,c_28,c_26,c_72]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2155,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(backward_subsumption_resolution,[status(thm)],[c_2070,c_1989]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2168,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.45/1.08      inference(backward_subsumption_resolution,[status(thm)],[c_2097,c_2155]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2215,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 1.45/1.08      | v1_xboole_0(X0)
% 1.45/1.08      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.45/1.08      inference(resolution,[status(thm)],[c_2124,c_2168]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3232,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.45/1.08      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 1.45/1.08      | v1_xboole_0(X0) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_2215]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3278,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.45/1.08      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.45/1.08      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 1.45/1.08      | v1_xboole_0(X0) = iProver_top ),
% 1.45/1.08      inference(light_normalisation,[status(thm)],[c_3232,c_2060]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3828,plain,
% 1.45/1.08      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
% 1.45/1.08      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 1.45/1.08      inference(equality_resolution,[status(thm)],[c_3278]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3829,plain,
% 1.45/1.08      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.45/1.08      | sK3 != sK3
% 1.45/1.08      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 1.45/1.08      inference(light_normalisation,[status(thm)],[c_3828,c_2611]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3830,plain,
% 1.45/1.08      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 1.45/1.08      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 1.45/1.08      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 1.45/1.08      inference(equality_resolution_simp,[status(thm)],[c_3829]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_0,plain,
% 1.45/1.08      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.45/1.08      inference(cnf_transformation,[],[f52]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3242,plain,
% 1.45/1.08      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_8,plain,
% 1.45/1.08      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | ~ v2_pre_topc(X0)
% 1.45/1.08      | ~ l1_pre_topc(X0) ),
% 1.45/1.08      inference(cnf_transformation,[],[f58]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_530,plain,
% 1.45/1.08      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.08      | v2_struct_0(X0)
% 1.45/1.08      | ~ l1_pre_topc(X0)
% 1.45/1.08      | sK2 != X0 ),
% 1.45/1.08      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_531,plain,
% 1.45/1.08      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | v2_struct_0(sK2)
% 1.45/1.08      | ~ l1_pre_topc(sK2) ),
% 1.45/1.08      inference(unflattening,[status(thm)],[c_530]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_66,plain,
% 1.45/1.08      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.45/1.08      | v2_struct_0(sK2)
% 1.45/1.08      | ~ v2_pre_topc(sK2)
% 1.45/1.08      | ~ l1_pre_topc(sK2) ),
% 1.45/1.08      inference(instantiation,[status(thm)],[c_8]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_533,plain,
% 1.45/1.08      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.45/1.08      inference(global_propositional_subsumption,
% 1.45/1.08                [status(thm)],
% 1.45/1.08                [c_531,c_28,c_27,c_26,c_66]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3235,plain,
% 1.45/1.08      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3257,plain,
% 1.45/1.08      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 1.45/1.08      inference(light_normalisation,[status(thm)],[c_3235,c_2060]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_4,plain,
% 1.45/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.45/1.08      | ~ r2_hidden(X2,X0)
% 1.45/1.08      | ~ v1_xboole_0(X1) ),
% 1.45/1.08      inference(cnf_transformation,[],[f55]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3239,plain,
% 1.45/1.08      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.45/1.08      | r2_hidden(X2,X0) != iProver_top
% 1.45/1.08      | v1_xboole_0(X1) != iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3570,plain,
% 1.45/1.08      ( r2_hidden(X0,sK1(sK2)) != iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
% 1.45/1.08      inference(superposition,[status(thm)],[c_3257,c_3239]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3835,plain,
% 1.45/1.08      ( v1_xboole_0(sK1(sK2)) = iProver_top
% 1.45/1.08      | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
% 1.45/1.08      inference(superposition,[status(thm)],[c_3242,c_3570]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3892,plain,
% 1.45/1.08      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 1.45/1.08      inference(global_propositional_subsumption,
% 1.45/1.08                [status(thm)],
% 1.45/1.08                [c_3488,c_29,c_30,c_31,c_36,c_70,c_3830,c_3835]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3,plain,
% 1.45/1.08      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.45/1.08      inference(cnf_transformation,[],[f54]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3240,plain,
% 1.45/1.08      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.45/1.08      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_2,plain,
% 1.45/1.08      ( k2_subset_1(X0) = X0 ),
% 1.45/1.08      inference(cnf_transformation,[],[f53]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3254,plain,
% 1.45/1.08      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.45/1.08      inference(light_normalisation,[status(thm)],[c_3240,c_2]) ).
% 1.45/1.08  
% 1.45/1.08  cnf(c_3897,plain,
% 1.45/1.08      ( $false ),
% 1.45/1.08      inference(forward_subsumption_resolution,[status(thm)],[c_3892,c_3254]) ).
% 1.45/1.08  
% 1.45/1.08  
% 1.45/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 1.45/1.08  
% 1.45/1.08  ------                               Statistics
% 1.45/1.08  
% 1.45/1.08  ------ General
% 1.45/1.08  
% 1.45/1.08  abstr_ref_over_cycles:                  0
% 1.45/1.08  abstr_ref_under_cycles:                 0
% 1.45/1.08  gc_basic_clause_elim:                   0
% 1.45/1.08  forced_gc_time:                         0
% 1.45/1.08  parsing_time:                           0.01
% 1.45/1.08  unif_index_cands_time:                  0.
% 1.45/1.08  unif_index_add_time:                    0.
% 1.45/1.08  orderings_time:                         0.
% 1.45/1.08  out_proof_time:                         0.016
% 1.45/1.08  total_time:                             0.173
% 1.45/1.08  num_of_symbols:                         59
% 1.45/1.08  num_of_terms:                           1947
% 1.45/1.08  
% 1.45/1.08  ------ Preprocessing
% 1.45/1.08  
% 1.45/1.08  num_of_splits:                          0
% 1.45/1.08  num_of_split_atoms:                     0
% 1.45/1.08  num_of_reused_defs:                     0
% 1.45/1.08  num_eq_ax_congr_red:                    10
% 1.45/1.08  num_of_sem_filtered_clauses:            1
% 1.45/1.08  num_of_subtypes:                        0
% 1.45/1.08  monotx_restored_types:                  0
% 1.45/1.08  sat_num_of_epr_types:                   0
% 1.45/1.08  sat_num_of_non_cyclic_types:            0
% 1.45/1.08  sat_guarded_non_collapsed_types:        0
% 1.45/1.08  num_pure_diseq_elim:                    0
% 1.45/1.08  simp_replaced_by:                       0
% 1.45/1.08  res_preprocessed:                       98
% 1.45/1.08  prep_upred:                             0
% 1.45/1.08  prep_unflattend:                        69
% 1.45/1.08  smt_new_axioms:                         0
% 1.45/1.08  pred_elim_cands:                        3
% 1.45/1.08  pred_elim:                              11
% 1.45/1.08  pred_elim_cl:                           13
% 1.45/1.08  pred_elim_cycles:                       22
% 1.45/1.08  merged_defs:                            2
% 1.45/1.08  merged_defs_ncl:                        0
% 1.45/1.08  bin_hyper_res:                          2
% 1.45/1.08  prep_cycles:                            4
% 1.45/1.08  pred_elim_time:                         0.088
% 1.45/1.08  splitting_time:                         0.
% 1.45/1.08  sem_filter_time:                        0.
% 1.45/1.08  monotx_time:                            0.
% 1.45/1.08  subtype_inf_time:                       0.
% 1.45/1.08  
% 1.45/1.08  ------ Problem properties
% 1.45/1.08  
% 1.45/1.08  clauses:                                14
% 1.45/1.08  conjectures:                            3
% 1.45/1.08  epr:                                    2
% 1.45/1.08  horn:                                   12
% 1.45/1.08  ground:                                 7
% 1.45/1.08  unary:                                  9
% 1.45/1.08  binary:                                 2
% 1.45/1.08  lits:                                   32
% 1.45/1.08  lits_eq:                                9
% 1.45/1.08  fd_pure:                                0
% 1.45/1.08  fd_pseudo:                              0
% 1.45/1.08  fd_cond:                                0
% 1.45/1.08  fd_pseudo_cond:                         0
% 1.45/1.08  ac_symbols:                             0
% 1.45/1.08  
% 1.45/1.08  ------ Propositional Solver
% 1.45/1.08  
% 1.45/1.08  prop_solver_calls:                      26
% 1.45/1.08  prop_fast_solver_calls:                 1484
% 1.45/1.08  smt_solver_calls:                       0
% 1.45/1.08  smt_fast_solver_calls:                  0
% 1.45/1.08  prop_num_of_clauses:                    767
% 1.45/1.08  prop_preprocess_simplified:             3020
% 1.45/1.08  prop_fo_subsumed:                       55
% 1.45/1.08  prop_solver_time:                       0.
% 1.45/1.08  smt_solver_time:                        0.
% 1.45/1.08  smt_fast_solver_time:                   0.
% 1.45/1.08  prop_fast_solver_time:                  0.
% 1.45/1.08  prop_unsat_core_time:                   0.
% 1.45/1.08  
% 1.45/1.08  ------ QBF
% 1.45/1.08  
% 1.45/1.08  qbf_q_res:                              0
% 1.45/1.08  qbf_num_tautologies:                    0
% 1.45/1.08  qbf_prep_cycles:                        0
% 1.45/1.08  
% 1.45/1.08  ------ BMC1
% 1.45/1.08  
% 1.45/1.08  bmc1_current_bound:                     -1
% 1.45/1.08  bmc1_last_solved_bound:                 -1
% 1.45/1.08  bmc1_unsat_core_size:                   -1
% 1.45/1.08  bmc1_unsat_core_parents_size:           -1
% 1.45/1.08  bmc1_merge_next_fun:                    0
% 1.45/1.08  bmc1_unsat_core_clauses_time:           0.
% 1.45/1.08  
% 1.45/1.08  ------ Instantiation
% 1.45/1.08  
% 1.45/1.08  inst_num_of_clauses:                    136
% 1.45/1.08  inst_num_in_passive:                    35
% 1.45/1.08  inst_num_in_active:                     88
% 1.45/1.08  inst_num_in_unprocessed:                13
% 1.45/1.08  inst_num_of_loops:                      90
% 1.45/1.08  inst_num_of_learning_restarts:          0
% 1.45/1.08  inst_num_moves_active_passive:          0
% 1.45/1.08  inst_lit_activity:                      0
% 1.45/1.08  inst_lit_activity_moves:                0
% 1.45/1.08  inst_num_tautologies:                   0
% 1.45/1.08  inst_num_prop_implied:                  0
% 1.45/1.08  inst_num_existing_simplified:           0
% 1.45/1.08  inst_num_eq_res_simplified:             0
% 1.45/1.08  inst_num_child_elim:                    0
% 1.45/1.08  inst_num_of_dismatching_blockings:      5
% 1.45/1.08  inst_num_of_non_proper_insts:           86
% 1.45/1.08  inst_num_of_duplicates:                 0
% 1.45/1.08  inst_inst_num_from_inst_to_res:         0
% 1.45/1.08  inst_dismatching_checking_time:         0.
% 1.45/1.08  
% 1.45/1.08  ------ Resolution
% 1.45/1.08  
% 1.45/1.08  res_num_of_clauses:                     0
% 1.45/1.08  res_num_in_passive:                     0
% 1.45/1.08  res_num_in_active:                      0
% 1.45/1.08  res_num_of_loops:                       102
% 1.45/1.08  res_forward_subset_subsumed:            13
% 1.45/1.08  res_backward_subset_subsumed:           0
% 1.45/1.08  res_forward_subsumed:                   0
% 1.45/1.08  res_backward_subsumed:                  0
% 1.45/1.08  res_forward_subsumption_resolution:     2
% 1.45/1.08  res_backward_subsumption_resolution:    4
% 1.45/1.08  res_clause_to_clause_subsumption:       158
% 1.45/1.08  res_orphan_elimination:                 0
% 1.45/1.08  res_tautology_del:                      11
% 1.45/1.08  res_num_eq_res_simplified:              1
% 1.45/1.08  res_num_sel_changes:                    0
% 1.45/1.08  res_moves_from_active_to_pass:          0
% 1.45/1.08  
% 1.45/1.08  ------ Superposition
% 1.45/1.08  
% 1.45/1.08  sup_time_total:                         0.
% 1.45/1.08  sup_time_generating:                    0.
% 1.45/1.08  sup_time_sim_full:                      0.
% 1.45/1.08  sup_time_sim_immed:                     0.
% 1.45/1.08  
% 1.45/1.08  sup_num_of_clauses:                     19
% 1.45/1.08  sup_num_in_active:                      17
% 1.45/1.08  sup_num_in_passive:                     2
% 1.45/1.08  sup_num_of_loops:                       17
% 1.45/1.08  sup_fw_superposition:                   4
% 1.45/1.08  sup_bw_superposition:                   1
% 1.45/1.08  sup_immediate_simplified:               2
% 1.45/1.08  sup_given_eliminated:                   0
% 1.45/1.08  comparisons_done:                       0
% 1.45/1.08  comparisons_avoided:                    0
% 1.45/1.08  
% 1.45/1.08  ------ Simplifications
% 1.45/1.08  
% 1.45/1.08  
% 1.45/1.08  sim_fw_subset_subsumed:                 0
% 1.45/1.08  sim_bw_subset_subsumed:                 0
% 1.45/1.08  sim_fw_subsumed:                        0
% 1.45/1.08  sim_bw_subsumed:                        0
% 1.45/1.08  sim_fw_subsumption_res:                 1
% 1.45/1.08  sim_bw_subsumption_res:                 0
% 1.45/1.08  sim_tautology_del:                      0
% 1.45/1.08  sim_eq_tautology_del:                   0
% 1.45/1.08  sim_eq_res_simp:                        2
% 1.45/1.08  sim_fw_demodulated:                     0
% 1.45/1.08  sim_bw_demodulated:                     0
% 1.45/1.08  sim_light_normalised:                   7
% 1.45/1.08  sim_joinable_taut:                      0
% 1.45/1.08  sim_joinable_simp:                      0
% 1.45/1.08  sim_ac_normalised:                      0
% 1.45/1.08  sim_smt_subsumption:                    0
% 1.45/1.08  
%------------------------------------------------------------------------------
