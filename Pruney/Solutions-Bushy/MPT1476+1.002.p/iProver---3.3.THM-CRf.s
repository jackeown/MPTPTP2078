%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1476+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:43 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  188 (2195 expanded)
%              Number of clauses        :  125 ( 761 expanded)
%              Number of leaves         :   18 ( 530 expanded)
%              Depth                    :   28
%              Number of atoms          :  567 (9391 expanded)
%              Number of equality atoms :  279 (1312 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <~> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f53,plain,
    ( ( ~ r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
      | ~ r1_orders_2(sK2,sK3,sK4) )
    & ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
      | r1_orders_2(sK2,sK3,sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f49,f52,f51,f50])).

fof(f81,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k8_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f45])).

fof(f58,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,
    ( ~ r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1181,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | k8_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1205,plain,
    ( k8_lattice3(X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2318,plain,
    ( k8_lattice3(sK2,sK4) = sK4
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1205])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1991,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k8_lattice3(X0,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1993,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k8_lattice3(sK2,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_2535,plain,
    ( k8_lattice3(sK2,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2318,c_29,c_27,c_1993])).

cnf(c_26,negated_conjecture,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1182,plain,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3)) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2537,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,k8_lattice3(sK2,sK3)) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2535,c_1182])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1180,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2319,plain,
    ( k8_lattice3(sK2,sK3) = sK3
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1205])).

cnf(c_1674,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k8_lattice3(X0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1676,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | k8_lattice3(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_2542,plain,
    ( k8_lattice3(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2319,c_29,c_28,c_1676])).

cnf(c_2654,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,sK3) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2537,c_2542])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1199,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1179,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1192,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1187,plain,
    ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2127,plain,
    ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = k4_relat_1(u1_orders_2(X0))
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1187])).

cnf(c_5353,plain,
    ( k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)) = k4_relat_1(u1_orders_2(sK2)) ),
    inference(superposition,[status(thm)],[c_1179,c_2127])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5512,plain,
    ( m1_subset_1(k4_relat_1(u1_orders_2(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5353,c_1196])).

cnf(c_30,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_57,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_59,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_5928,plain,
    ( m1_subset_1(k4_relat_1(u1_orders_2(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5512,c_30,c_59])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | l1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5934,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK2),k4_relat_1(u1_orders_2(sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5928,c_1198])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1206,plain,
    ( g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = k7_lattice3(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2361,plain,
    ( g1_orders_2(u1_struct_0(sK2),k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2))) = k7_lattice3(sK2) ),
    inference(superposition,[status(thm)],[c_1179,c_1206])).

cnf(c_5510,plain,
    ( g1_orders_2(u1_struct_0(sK2),k4_relat_1(u1_orders_2(sK2))) = k7_lattice3(sK2) ),
    inference(demodulation,[status(thm)],[c_5353,c_2361])).

cnf(c_5942,plain,
    ( l1_orders_2(k7_lattice3(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5934,c_5510])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1208,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6394,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK2)),u1_orders_2(k7_lattice3(sK2))) = k7_lattice3(sK2)
    | v1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5942,c_1208])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_67,plain,
    ( l1_orders_2(k7_lattice3(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | v1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_446,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | k7_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_447,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(k7_lattice3(X0))
    | g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = k7_lattice3(X0) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_449,plain,
    ( ~ l1_orders_2(k7_lattice3(sK2))
    | ~ l1_orders_2(sK2)
    | g1_orders_2(u1_struct_0(k7_lattice3(sK2)),u1_orders_2(k7_lattice3(sK2))) = k7_lattice3(sK2) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_6730,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK2)),u1_orders_2(k7_lattice3(sK2))) = k7_lattice3(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6394,c_29,c_67,c_449])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1191,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2771,plain,
    ( k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)) = X0
    | g1_orders_2(X1,X0) != k7_lattice3(sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_1191])).

cnf(c_2037,plain,
    ( m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2038,plain,
    ( m1_subset_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2037])).

cnf(c_2040,plain,
    ( m1_subset_1(k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(c_2772,plain,
    ( k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)) = X0
    | g1_orders_2(X1,X0) != k7_lattice3(sK2)
    | m1_subset_1(k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_1191])).

cnf(c_3292,plain,
    ( g1_orders_2(X1,X0) != k7_lattice3(sK2)
    | k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2771,c_30,c_59,c_2040,c_2772])).

cnf(c_3293,plain,
    ( k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)) = X0
    | g1_orders_2(X1,X0) != k7_lattice3(sK2) ),
    inference(renaming,[status(thm)],[c_3292])).

cnf(c_5509,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | k4_relat_1(u1_orders_2(sK2)) = X1 ),
    inference(demodulation,[status(thm)],[c_5353,c_3293])).

cnf(c_6738,plain,
    ( k4_relat_1(u1_orders_2(sK2)) = u1_orders_2(k7_lattice3(sK2)) ),
    inference(superposition,[status(thm)],[c_6730,c_5509])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1201,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7247,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6738,c_1201])).

cnf(c_7248,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | v1_relat_1(u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7247,c_6738])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1290,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1379,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_1380,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1379])).

cnf(c_1207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2470,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(k3_relset_1(X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1207])).

cnf(c_5516,plain,
    ( v1_relat_1(k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_2470])).

cnf(c_5581,plain,
    ( v1_relat_1(k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5353,c_5516])).

cnf(c_5799,plain,
    ( v1_relat_1(k4_relat_1(u1_orders_2(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5581,c_30])).

cnf(c_7178,plain,
    ( v1_relat_1(u1_orders_2(k7_lattice3(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6738,c_5799])).

cnf(c_13702,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7248,c_30,c_59,c_1380,c_7178])).

cnf(c_13710,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_13702])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1190,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2728,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_1190])).

cnf(c_2729,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(k3_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_orders_2(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_1190])).

cnf(c_3287,plain,
    ( u1_struct_0(sK2) = X0
    | g1_orders_2(X0,X1) != k7_lattice3(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_30,c_59,c_2040,c_2729])).

cnf(c_3288,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(sK2)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_3287])).

cnf(c_6739,plain,
    ( u1_struct_0(k7_lattice3(sK2)) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_6730,c_3288])).

cnf(c_13714,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13710,c_6739])).

cnf(c_66,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(k7_lattice3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_68,plain,
    ( l1_orders_2(k7_lattice3(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_14746,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13714,c_30,c_68])).

cnf(c_14747,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14746])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1200,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14754,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14747,c_1200])).

cnf(c_24360,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X1,X0) = iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14754,c_30])).

cnf(c_24361,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24360])).

cnf(c_24366,plain,
    ( r1_orders_2(sK2,sK3,sK4) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_24361])).

cnf(c_2123,plain,
    ( v1_relat_1(u1_orders_2(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1207])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1188,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2219,plain,
    ( k4_relat_1(k4_relat_1(u1_orders_2(X0))) = u1_orders_2(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_1188])).

cnf(c_2225,plain,
    ( k4_relat_1(k4_relat_1(u1_orders_2(sK2))) = u1_orders_2(sK2) ),
    inference(superposition,[status(thm)],[c_1179,c_2219])).

cnf(c_2998,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(k4_relat_1(u1_orders_2(sK2)))) != iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2225,c_1201])).

cnf(c_2999,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2998,c_2225])).

cnf(c_3369,plain,
    ( v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2999,c_30,c_59,c_1380])).

cnf(c_3370,plain,
    ( r2_hidden(k4_tarski(X0,X1),k4_relat_1(u1_orders_2(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(u1_orders_2(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3369])).

cnf(c_7197,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | v1_relat_1(u1_orders_2(k7_lattice3(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6738,c_3370])).

cnf(c_8136,plain,
    ( r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7197,c_7178])).

cnf(c_8137,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(k7_lattice3(sK2))) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8136])).

cnf(c_8143,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k7_lattice3(sK2))) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8137,c_1200])).

cnf(c_8146,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(k7_lattice3(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8143,c_6739])).

cnf(c_14530,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8146,c_30,c_68])).

cnf(c_14531,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14530])).

cnf(c_14538,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_14531])).

cnf(c_24059,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14538,c_30])).

cnf(c_24060,plain,
    ( r1_orders_2(k7_lattice3(sK2),X0,X1) = iProver_top
    | r1_orders_2(sK2,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24059])).

cnf(c_25,negated_conjecture,
    ( ~ r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3))
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1183,plain,
    ( r1_orders_2(k7_lattice3(sK2),k8_lattice3(sK2,sK4),k8_lattice3(sK2,sK3)) != iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2538,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,k8_lattice3(sK2,sK3)) != iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2535,c_1183])).

cnf(c_2651,plain,
    ( r1_orders_2(k7_lattice3(sK2),sK4,sK3) != iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2538,c_2542])).

cnf(c_24066,plain,
    ( r1_orders_2(sK2,sK3,sK4) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24060,c_2651])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24366,c_24066,c_32,c_31])).


%------------------------------------------------------------------------------
