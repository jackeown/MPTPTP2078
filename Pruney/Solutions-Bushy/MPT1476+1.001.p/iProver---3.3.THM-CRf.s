%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:43 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  176 (2423 expanded)
%              Number of clauses        :  114 ( 833 expanded)
%              Number of leaves         :   17 ( 580 expanded)
%              Depth                    :   31
%              Number of atoms          :  551 (10484 expanded)
%              Number of equality atoms :  260 (1551 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <~> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
            | ~ r1_orders_2(X0,X1,X2) )
          & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
            | r1_orders_2(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,sK4),k8_lattice3(X0,X1))
          | ~ r1_orders_2(X0,X1,sK4) )
        & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,sK4),k8_lattice3(X0,X1))
          | r1_orders_2(X0,X1,sK4) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,sK3))
              | ~ r1_orders_2(X0,sK3,X2) )
            & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,sK3))
              | r1_orders_2(X0,sK3,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                  | r1_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,X2),k8_lattice3(sK2,X1))
                | ~ r1_orders_2(sK2,X1,X2) )
              & ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,X2),k8_lattice3(sK2,X1))
                | r1_orders_2(sK2,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
      | ~ r1_orders_2(sK2,sK3,sK4) )
    & ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
      | r1_orders_2(sK2,sK3,sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).

fof(f74,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).

fof(f54,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f76,plain,
    ( ~ r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1302,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | k8_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1322,plain,
    ( k8_lattice3(X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2419,plain,
    ( k8_lattice3(sK2,sK4) = sK4
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_1322])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2006,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k8_lattice3(X0,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k8_lattice3(sK2,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_2556,plain,
    ( k8_lattice3(sK2,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2419,c_26,c_24,c_2008])).

cnf(c_23,negated_conjecture,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1303,plain,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3)) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2558,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,k8_lattice3(sK2,sK3)) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2556,c_1303])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1301,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2420,plain,
    ( k8_lattice3(sK2,sK3) = sK3
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1322])).

cnf(c_1705,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k8_lattice3(X0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1707,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k8_lattice3(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_2629,plain,
    ( k8_lattice3(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2420,c_26,c_25,c_1707])).

cnf(c_2911,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,sK3) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2558,c_2629])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1316,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1300,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1312,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1308,plain,
    ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2203,plain,
    ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = k4_relat_1(u1_orders_2(X0))
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1308])).

cnf(c_4089,plain,
    ( k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)) = k4_relat_1(u1_orders_2(sK2)) ),
    inference(superposition,[status(thm)],[c_1300,c_2203])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1323,plain,
    ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2469,plain,
    ( g1_orders_2(u1_struct_0(sK2),k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2))) = k7_lattice3(sK2) ),
    inference(superposition,[status(thm)],[c_1300,c_1323])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | v1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_374,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | k7_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_375,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(k7_lattice3(X0))
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_379,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_11])).

cnf(c_1299,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1716,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK2)),u1_orders_2(k7_lattice3(sK2))) = k7_lattice3(sK2) ),
    inference(superposition,[status(thm)],[c_1300,c_1299])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1311,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2547,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_orders_2(k7_lattice3(sK2)) = X1
    | m1_subset_1(u1_orders_2(k7_lattice3(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK2)),u1_struct_0(k7_lattice3(sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1311])).

cnf(c_27,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_60,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(k7_lattice3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_62,plain,
    ( l1_orders_2(k7_lattice3(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1310,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2474,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_struct_0(k7_lattice3(sK2)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1310])).

cnf(c_3433,plain,
    ( u1_struct_0(k7_lattice3(sK2)) = u1_struct_0(sK2)
    | m1_subset_1(k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_2474])).

cnf(c_2631,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_1310])).

cnf(c_3385,plain,
    ( u1_struct_0(k7_lattice3(sK2)) = u1_struct_0(sK2)
    | m1_subset_1(u1_orders_2(k7_lattice3(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK2)),u1_struct_0(k7_lattice3(sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_2631])).

cnf(c_3388,plain,
    ( u1_struct_0(k7_lattice3(sK2)) = u1_struct_0(sK2)
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_3385])).

cnf(c_3469,plain,
    ( u1_struct_0(k7_lattice3(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3433,c_27,c_62,c_3388])).

cnf(c_3476,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_1312])).

cnf(c_3474,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(k7_lattice3(sK2))) = k7_lattice3(sK2) ),
    inference(demodulation,[status(thm)],[c_3469,c_1716])).

cnf(c_3489,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_orders_2(k7_lattice3(sK2)) = X1
    | m1_subset_1(u1_orders_2(k7_lattice3(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3474,c_1311])).

cnf(c_3924,plain,
    ( u1_orders_2(k7_lattice3(sK2)) = X1
    | g1_orders_2(X0,X1) != k7_lattice3(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2547,c_27,c_62,c_3476,c_3489])).

cnf(c_3925,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_orders_2(k7_lattice3(sK2)) = X1 ),
    inference(renaming,[status(thm)],[c_3924])).

cnf(c_3927,plain,
    ( k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)) = u1_orders_2(k7_lattice3(sK2)) ),
    inference(superposition,[status(thm)],[c_2469,c_3925])).

cnf(c_4090,plain,
    ( k4_relat_1(u1_orders_2(sK2)) = u1_orders_2(k7_lattice3(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4089,c_3927])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1318,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4120,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4090,c_1318])).

cnf(c_4121,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | v1_relat_1(u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4120,c_4090])).

cnf(c_51,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_53,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1402,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1489,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1490,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1315,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4118,plain,
    ( v1_relat_1(u1_orders_2(k7_lattice3(sK2))) = iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4090,c_1315])).

cnf(c_5765,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4121,c_27,c_53,c_1490,c_4118])).

cnf(c_5773,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_5765])).

cnf(c_5775,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5773,c_3469])).

cnf(c_5912,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5775,c_27,c_62])).

cnf(c_5913,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5912])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1317,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5919,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5913,c_1317])).

cnf(c_23110,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X1,X0) = iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5919,c_27])).

cnf(c_23111,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23110])).

cnf(c_23116,plain,
    ( r1_orders_2(sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_23111])).

cnf(c_1324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2202,plain,
    ( v1_relat_1(u1_orders_2(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1324])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1309,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2213,plain,
    ( k4_relat_1(k4_relat_1(u1_orders_2(X0))) = u1_orders_2(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_1309])).

cnf(c_2319,plain,
    ( k4_relat_1(k4_relat_1(u1_orders_2(sK2))) = u1_orders_2(sK2) ),
    inference(superposition,[status(thm)],[c_1300,c_2213])).

cnf(c_3078,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(k4_relat_1(u1_orders_2(sK2)))) != iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_1318])).

cnf(c_3079,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3078,c_2319])).

cnf(c_1693,plain,
    ( v1_relat_1(k4_relat_1(u1_orders_2(sK2)))
    | ~ v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1694,plain,
    ( v1_relat_1(k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2356,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2)))
    | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
    | ~ v1_relat_1(k4_relat_1(u1_orders_2(sK2)))
    | ~ v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2357,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2356])).

cnf(c_4637,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3079,c_27,c_53,c_1490,c_1694,c_2357])).

cnf(c_4643,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4637,c_4090])).

cnf(c_4648,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4643,c_1317])).

cnf(c_4651,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4648,c_3469])).

cnf(c_5787,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4651,c_27,c_62])).

cnf(c_5788,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5787])).

cnf(c_5795,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_5788])).

cnf(c_21382,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5795,c_27])).

cnf(c_21383,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21382])).

cnf(c_22,negated_conjecture,
    ( ~ r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1304,plain,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3)) != iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2559,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,k8_lattice3(sK2,sK3)) != iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2556,c_1304])).

cnf(c_2784,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,sK3) != iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2559,c_2629])).

cnf(c_21389,plain,
    ( r1_orders_2(sK2,sK3,sK4) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21383,c_2784])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23116,c_21389,c_29,c_28])).


%------------------------------------------------------------------------------
