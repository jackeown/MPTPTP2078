%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1143+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:00 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 778 expanded)
%              Number of clauses        :   71 ( 233 expanded)
%              Number of leaves         :   18 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          :  464 (3422 expanded)
%              Number of equality atoms :  104 ( 214 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),sK5),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),sK5),X0) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),k1_zfmisc_1(u1_struct_0(sK4)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK4),X1),sK4) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f47,f46])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X0)
        & r2_hidden(sK0(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X0)
              & r2_hidden(sK0(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X3),X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1738,plain,
    ( r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r7_relat_2(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1741,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3143,plain,
    ( sK3(X0,k1_tarski(X1)) = X1
    | r7_relat_2(X0,k1_tarski(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1741])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1735,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_318,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_319,plain,
    ( ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_46,plain,
    ( l1_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_321,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_27,c_25,c_40,c_46])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_321])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1732,plain,
    ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_2074,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    inference(superposition,[status(thm)],[c_1735,c_1732])).

cnf(c_23,negated_conjecture,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1,plain,
    ( ~ r7_relat_2(u1_orders_2(X0),X1)
    | v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_412,plain,
    ( ~ r7_relat_2(u1_orders_2(X0),X1)
    | v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_25])).

cnf(c_413,plain,
    ( ~ r7_relat_2(u1_orders_2(sK4),X0)
    | v6_orders_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_438,plain,
    ( ~ r7_relat_2(u1_orders_2(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_domain_1(u1_struct_0(sK4),sK5) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_413])).

cnf(c_439,plain,
    ( ~ r7_relat_2(u1_orders_2(sK4),k6_domain_1(u1_struct_0(sK4),sK5))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_1729,plain,
    ( r7_relat_2(u1_orders_2(sK4),k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_440,plain,
    ( r7_relat_2(u1_orders_2(sK4),k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_321])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_1896,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_1897,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1896])).

cnf(c_1922,plain,
    ( r7_relat_2(u1_orders_2(sK4),k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1729,c_31,c_440,c_1897])).

cnf(c_2076,plain,
    ( r7_relat_2(u1_orders_2(sK4),k1_tarski(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2074,c_1922])).

cnf(c_4360,plain,
    ( sK3(u1_orders_2(sK4),k1_tarski(sK5)) = sK5
    | v1_relat_1(u1_orders_2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3143,c_2076])).

cnf(c_30,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_42,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_44,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1902,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | v1_relat_1(u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1903,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1902])).

cnf(c_4767,plain,
    ( sK3(u1_orders_2(sK4),k1_tarski(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4360,c_30,c_44,c_1903])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1739,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) != iProver_top
    | r7_relat_2(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4772,plain,
    ( r2_hidden(k4_tarski(sK2(u1_orders_2(sK4),k1_tarski(sK5)),sK5),u1_orders_2(sK4)) != iProver_top
    | r7_relat_2(u1_orders_2(sK4),k1_tarski(sK5)) = iProver_top
    | v1_relat_1(u1_orders_2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4767,c_1739])).

cnf(c_15,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r7_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1737,plain,
    ( r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r7_relat_2(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2932,plain,
    ( sK2(X0,k1_tarski(X1)) = X1
    | r7_relat_2(X0,k1_tarski(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1741])).

cnf(c_4318,plain,
    ( sK2(u1_orders_2(sK4),k1_tarski(sK5)) = sK5
    | v1_relat_1(u1_orders_2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2932,c_2076])).

cnf(c_4644,plain,
    ( sK2(u1_orders_2(sK4),k1_tarski(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4318,c_30,c_44,c_1903])).

cnf(c_4776,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),u1_orders_2(sK4)) != iProver_top
    | r7_relat_2(u1_orders_2(sK4),k1_tarski(sK5)) = iProver_top
    | v1_relat_1(u1_orders_2(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4772,c_4644])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),X2)
    | ~ r1_relat_2(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2007,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK4))
    | ~ r1_relat_2(u1_orders_2(sK4),X1)
    | ~ v1_relat_1(u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2418,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK4))
    | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK4))
    | ~ r1_relat_2(u1_orders_2(sK4),u1_struct_0(sK4))
    | ~ v1_relat_1(u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_2470,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),u1_orders_2(sK4))
    | ~ r2_hidden(sK5,u1_struct_0(sK4))
    | ~ r1_relat_2(u1_orders_2(sK4),u1_struct_0(sK4))
    | ~ v1_relat_1(u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_2418])).

cnf(c_2471,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),u1_orders_2(sK4)) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top
    | r1_relat_2(u1_orders_2(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_relat_1(u1_orders_2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2470])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_345,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_321])).

cnf(c_346,plain,
    ( r2_hidden(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1893,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1894,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_11,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_66,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_68,plain,
    ( r1_relat_2(u1_orders_2(sK4),u1_struct_0(sK4)) = iProver_top
    | v3_orders_2(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,plain,
    ( v3_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4776,c_2471,c_2076,c_1903,c_1894,c_68,c_44,c_31,c_30,c_29])).


%------------------------------------------------------------------------------
