%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:02 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 777 expanded)
%              Number of clauses        :   70 ( 232 expanded)
%              Number of leaves         :   16 ( 186 expanded)
%              Depth                    :   21
%              Number of atoms          :  446 (3406 expanded)
%              Number of equality atoms :   96 ( 205 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),sK4),X0) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK3)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),X1),sK3) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f46,f45])).

fof(f73,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( r7_relat_2(X0,X1)
    | r2_hidden(sK2(X0,X1),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1496,plain,
    ( r7_relat_2(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1501,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2802,plain,
    ( sK2(X0,k1_tarski(X1)) = X1
    | r7_relat_2(X0,k1_tarski(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1501])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1493,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_309,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_18,c_7])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_348,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_26])).

cnf(c_349,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_42,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_75,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_351,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_26,c_24,c_42,c_75])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_351])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_1492,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_1685,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) ),
    inference(superposition,[status(thm)],[c_1493,c_1492])).

cnf(c_8,plain,
    ( ~ r7_relat_2(u1_orders_2(X0),X1)
    | v6_orders_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_407,plain,
    ( ~ r7_relat_2(u1_orders_2(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(X0)
    | k6_domain_1(u1_struct_0(sK3),sK4) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_408,plain,
    ( ~ r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_410,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_24])).

cnf(c_411,plain,
    ( ~ r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_1489,plain,
    ( r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_29,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_409,plain,
    ( r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_351])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1630,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_1631,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1630])).

cnf(c_1665,plain,
    ( r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1489,c_29,c_30,c_409,c_1631])).

cnf(c_1813,plain,
    ( r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1685,c_1665])).

cnf(c_3341,plain,
    ( sK2(u1_orders_2(sK3),k1_tarski(sK4)) = sK4
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2802,c_1813])).

cnf(c_19,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_38,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_40,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1642,plain,
    ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1643,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_3438,plain,
    ( sK2(u1_orders_2(sK3),k1_tarski(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3341,c_29,c_40,c_1643])).

cnf(c_13,plain,
    ( r7_relat_2(X0,X1)
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1495,plain,
    ( r7_relat_2(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2778,plain,
    ( sK1(X0,k1_tarski(X1)) = X1
    | r7_relat_2(X0,k1_tarski(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1501])).

cnf(c_3164,plain,
    ( sK1(u1_orders_2(sK3),k1_tarski(sK4)) = sK4
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2778,c_1813])).

cnf(c_3233,plain,
    ( sK1(u1_orders_2(sK3),k1_tarski(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3164,c_29,c_40,c_1643])).

cnf(c_11,plain,
    ( r7_relat_2(X0,X1)
    | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1497,plain,
    ( r7_relat_2(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3238,plain,
    ( r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK4,sK2(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3)) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_1497])).

cnf(c_3331,plain,
    ( r2_hidden(k4_tarski(sK4,sK2(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3238,c_29,c_40,c_1643,c_1813])).

cnf(c_3441,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3438,c_3331])).

cnf(c_21,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_327,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_328,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_332,plain,
    ( r1_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_26,c_24])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_431,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_432,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(X0,X2),u1_orders_2(sK3))
    | X2 != X1
    | X0 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_432])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_1639,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_1640,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3441,c_1640,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.29  % Computer   : n001.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 20:29:45 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.30  % Running in FOF mode
% 1.91/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/0.94  
% 1.91/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.91/0.94  
% 1.91/0.94  ------  iProver source info
% 1.91/0.94  
% 1.91/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.91/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.91/0.94  git: non_committed_changes: false
% 1.91/0.94  git: last_make_outside_of_git: false
% 1.91/0.94  
% 1.91/0.94  ------ 
% 1.91/0.94  
% 1.91/0.94  ------ Input Options
% 1.91/0.94  
% 1.91/0.94  --out_options                           all
% 1.91/0.94  --tptp_safe_out                         true
% 1.91/0.94  --problem_path                          ""
% 1.91/0.94  --include_path                          ""
% 1.91/0.94  --clausifier                            res/vclausify_rel
% 1.91/0.94  --clausifier_options                    --mode clausify
% 1.91/0.94  --stdin                                 false
% 1.91/0.94  --stats_out                             all
% 1.91/0.94  
% 1.91/0.94  ------ General Options
% 1.91/0.94  
% 1.91/0.94  --fof                                   false
% 1.91/0.94  --time_out_real                         305.
% 1.91/0.94  --time_out_virtual                      -1.
% 1.91/0.94  --symbol_type_check                     false
% 1.91/0.94  --clausify_out                          false
% 1.91/0.94  --sig_cnt_out                           false
% 1.91/0.94  --trig_cnt_out                          false
% 1.91/0.94  --trig_cnt_out_tolerance                1.
% 1.91/0.94  --trig_cnt_out_sk_spl                   false
% 1.91/0.94  --abstr_cl_out                          false
% 1.91/0.94  
% 1.91/0.94  ------ Global Options
% 1.91/0.94  
% 1.91/0.94  --schedule                              default
% 1.91/0.94  --add_important_lit                     false
% 1.91/0.94  --prop_solver_per_cl                    1000
% 1.91/0.94  --min_unsat_core                        false
% 1.91/0.94  --soft_assumptions                      false
% 1.91/0.94  --soft_lemma_size                       3
% 1.91/0.94  --prop_impl_unit_size                   0
% 1.91/0.94  --prop_impl_unit                        []
% 1.91/0.94  --share_sel_clauses                     true
% 1.91/0.94  --reset_solvers                         false
% 1.91/0.94  --bc_imp_inh                            [conj_cone]
% 1.91/0.94  --conj_cone_tolerance                   3.
% 1.91/0.94  --extra_neg_conj                        none
% 1.91/0.94  --large_theory_mode                     true
% 1.91/0.94  --prolific_symb_bound                   200
% 1.91/0.94  --lt_threshold                          2000
% 1.91/0.94  --clause_weak_htbl                      true
% 1.91/0.94  --gc_record_bc_elim                     false
% 1.91/0.94  
% 1.91/0.94  ------ Preprocessing Options
% 1.91/0.94  
% 1.91/0.94  --preprocessing_flag                    true
% 1.91/0.94  --time_out_prep_mult                    0.1
% 1.91/0.94  --splitting_mode                        input
% 1.91/0.94  --splitting_grd                         true
% 1.91/0.94  --splitting_cvd                         false
% 1.91/0.94  --splitting_cvd_svl                     false
% 1.91/0.94  --splitting_nvd                         32
% 1.91/0.94  --sub_typing                            true
% 1.91/0.94  --prep_gs_sim                           true
% 1.91/0.94  --prep_unflatten                        true
% 1.91/0.94  --prep_res_sim                          true
% 1.91/0.94  --prep_upred                            true
% 1.91/0.94  --prep_sem_filter                       exhaustive
% 1.91/0.94  --prep_sem_filter_out                   false
% 1.91/0.94  --pred_elim                             true
% 1.91/0.94  --res_sim_input                         true
% 1.91/0.94  --eq_ax_congr_red                       true
% 1.91/0.94  --pure_diseq_elim                       true
% 1.91/0.94  --brand_transform                       false
% 1.91/0.94  --non_eq_to_eq                          false
% 1.91/0.94  --prep_def_merge                        true
% 1.91/0.94  --prep_def_merge_prop_impl              false
% 1.91/0.94  --prep_def_merge_mbd                    true
% 1.91/0.94  --prep_def_merge_tr_red                 false
% 1.91/0.94  --prep_def_merge_tr_cl                  false
% 1.91/0.94  --smt_preprocessing                     true
% 1.91/0.94  --smt_ac_axioms                         fast
% 1.91/0.94  --preprocessed_out                      false
% 1.91/0.94  --preprocessed_stats                    false
% 1.91/0.94  
% 1.91/0.94  ------ Abstraction refinement Options
% 1.91/0.94  
% 1.91/0.94  --abstr_ref                             []
% 1.91/0.94  --abstr_ref_prep                        false
% 1.91/0.94  --abstr_ref_until_sat                   false
% 1.91/0.94  --abstr_ref_sig_restrict                funpre
% 1.91/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/0.94  --abstr_ref_under                       []
% 1.91/0.94  
% 1.91/0.94  ------ SAT Options
% 1.91/0.94  
% 1.91/0.94  --sat_mode                              false
% 1.91/0.94  --sat_fm_restart_options                ""
% 1.91/0.94  --sat_gr_def                            false
% 1.91/0.94  --sat_epr_types                         true
% 1.91/0.94  --sat_non_cyclic_types                  false
% 1.91/0.94  --sat_finite_models                     false
% 1.91/0.94  --sat_fm_lemmas                         false
% 1.91/0.94  --sat_fm_prep                           false
% 1.91/0.94  --sat_fm_uc_incr                        true
% 1.91/0.94  --sat_out_model                         small
% 1.91/0.94  --sat_out_clauses                       false
% 1.91/0.94  
% 1.91/0.94  ------ QBF Options
% 1.91/0.94  
% 1.91/0.94  --qbf_mode                              false
% 1.91/0.94  --qbf_elim_univ                         false
% 1.91/0.94  --qbf_dom_inst                          none
% 1.91/0.94  --qbf_dom_pre_inst                      false
% 1.91/0.94  --qbf_sk_in                             false
% 1.91/0.94  --qbf_pred_elim                         true
% 1.91/0.94  --qbf_split                             512
% 1.91/0.94  
% 1.91/0.94  ------ BMC1 Options
% 1.91/0.94  
% 1.91/0.94  --bmc1_incremental                      false
% 1.91/0.94  --bmc1_axioms                           reachable_all
% 1.91/0.94  --bmc1_min_bound                        0
% 1.91/0.94  --bmc1_max_bound                        -1
% 1.91/0.94  --bmc1_max_bound_default                -1
% 1.91/0.94  --bmc1_symbol_reachability              true
% 1.91/0.94  --bmc1_property_lemmas                  false
% 1.91/0.94  --bmc1_k_induction                      false
% 1.91/0.94  --bmc1_non_equiv_states                 false
% 1.91/0.94  --bmc1_deadlock                         false
% 1.91/0.94  --bmc1_ucm                              false
% 1.91/0.94  --bmc1_add_unsat_core                   none
% 1.91/0.94  --bmc1_unsat_core_children              false
% 1.91/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/0.94  --bmc1_out_stat                         full
% 1.91/0.94  --bmc1_ground_init                      false
% 1.91/0.94  --bmc1_pre_inst_next_state              false
% 1.91/0.94  --bmc1_pre_inst_state                   false
% 1.91/0.94  --bmc1_pre_inst_reach_state             false
% 1.91/0.94  --bmc1_out_unsat_core                   false
% 1.91/0.94  --bmc1_aig_witness_out                  false
% 1.91/0.94  --bmc1_verbose                          false
% 1.91/0.94  --bmc1_dump_clauses_tptp                false
% 1.91/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.91/0.94  --bmc1_dump_file                        -
% 1.91/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.91/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.91/0.94  --bmc1_ucm_extend_mode                  1
% 1.91/0.94  --bmc1_ucm_init_mode                    2
% 1.91/0.94  --bmc1_ucm_cone_mode                    none
% 1.91/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.91/0.94  --bmc1_ucm_relax_model                  4
% 1.91/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.91/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/0.94  --bmc1_ucm_layered_model                none
% 1.91/0.94  --bmc1_ucm_max_lemma_size               10
% 1.91/0.94  
% 1.91/0.94  ------ AIG Options
% 1.91/0.94  
% 1.91/0.94  --aig_mode                              false
% 1.91/0.94  
% 1.91/0.94  ------ Instantiation Options
% 1.91/0.94  
% 1.91/0.94  --instantiation_flag                    true
% 1.91/0.94  --inst_sos_flag                         false
% 1.91/0.94  --inst_sos_phase                        true
% 1.91/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/0.94  --inst_lit_sel_side                     num_symb
% 1.91/0.94  --inst_solver_per_active                1400
% 1.91/0.94  --inst_solver_calls_frac                1.
% 1.91/0.94  --inst_passive_queue_type               priority_queues
% 1.91/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/0.94  --inst_passive_queues_freq              [25;2]
% 1.91/0.94  --inst_dismatching                      true
% 1.91/0.94  --inst_eager_unprocessed_to_passive     true
% 1.91/0.94  --inst_prop_sim_given                   true
% 1.91/0.94  --inst_prop_sim_new                     false
% 1.91/0.94  --inst_subs_new                         false
% 1.91/0.94  --inst_eq_res_simp                      false
% 1.91/0.94  --inst_subs_given                       false
% 1.91/0.94  --inst_orphan_elimination               true
% 1.91/0.94  --inst_learning_loop_flag               true
% 1.91/0.94  --inst_learning_start                   3000
% 1.91/0.94  --inst_learning_factor                  2
% 1.91/0.94  --inst_start_prop_sim_after_learn       3
% 1.91/0.94  --inst_sel_renew                        solver
% 1.91/0.94  --inst_lit_activity_flag                true
% 1.91/0.94  --inst_restr_to_given                   false
% 1.91/0.94  --inst_activity_threshold               500
% 1.91/0.94  --inst_out_proof                        true
% 1.91/0.94  
% 1.91/0.94  ------ Resolution Options
% 1.91/0.94  
% 1.91/0.94  --resolution_flag                       true
% 1.91/0.94  --res_lit_sel                           adaptive
% 1.91/0.94  --res_lit_sel_side                      none
% 1.91/0.94  --res_ordering                          kbo
% 1.91/0.94  --res_to_prop_solver                    active
% 1.91/0.94  --res_prop_simpl_new                    false
% 1.91/0.94  --res_prop_simpl_given                  true
% 1.91/0.94  --res_passive_queue_type                priority_queues
% 1.91/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/0.94  --res_passive_queues_freq               [15;5]
% 1.91/0.94  --res_forward_subs                      full
% 1.91/0.94  --res_backward_subs                     full
% 1.91/0.94  --res_forward_subs_resolution           true
% 1.91/0.94  --res_backward_subs_resolution          true
% 1.91/0.94  --res_orphan_elimination                true
% 1.91/0.94  --res_time_limit                        2.
% 1.91/0.94  --res_out_proof                         true
% 1.91/0.94  
% 1.91/0.94  ------ Superposition Options
% 1.91/0.94  
% 1.91/0.94  --superposition_flag                    true
% 1.91/0.94  --sup_passive_queue_type                priority_queues
% 1.91/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.91/0.94  --demod_completeness_check              fast
% 1.91/0.94  --demod_use_ground                      true
% 1.91/0.94  --sup_to_prop_solver                    passive
% 1.91/0.94  --sup_prop_simpl_new                    true
% 1.91/0.94  --sup_prop_simpl_given                  true
% 1.91/0.94  --sup_fun_splitting                     false
% 1.91/0.94  --sup_smt_interval                      50000
% 1.91/0.94  
% 1.91/0.94  ------ Superposition Simplification Setup
% 1.91/0.94  
% 1.91/0.94  --sup_indices_passive                   []
% 1.91/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.94  --sup_full_bw                           [BwDemod]
% 1.91/0.94  --sup_immed_triv                        [TrivRules]
% 1.91/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.94  --sup_immed_bw_main                     []
% 1.91/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.95  
% 1.91/0.95  ------ Combination Options
% 1.91/0.95  
% 1.91/0.95  --comb_res_mult                         3
% 1.91/0.95  --comb_sup_mult                         2
% 1.91/0.95  --comb_inst_mult                        10
% 1.91/0.95  
% 1.91/0.95  ------ Debug Options
% 1.91/0.95  
% 1.91/0.95  --dbg_backtrace                         false
% 1.91/0.95  --dbg_dump_prop_clauses                 false
% 1.91/0.95  --dbg_dump_prop_clauses_file            -
% 1.91/0.95  --dbg_out_stat                          false
% 1.91/0.95  ------ Parsing...
% 1.91/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/0.95  
% 1.91/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.91/0.95  
% 1.91/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/0.95  
% 1.91/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/0.95  ------ Proving...
% 1.91/0.95  ------ Problem Properties 
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  clauses                                 18
% 1.91/0.95  conjectures                             1
% 1.91/0.95  EPR                                     0
% 1.91/0.95  Horn                                    14
% 1.91/0.95  unary                                   3
% 1.91/0.95  binary                                  8
% 1.91/0.95  lits                                    43
% 1.91/0.95  lits eq                                 6
% 1.91/0.95  fd_pure                                 0
% 1.91/0.95  fd_pseudo                               0
% 1.91/0.95  fd_cond                                 0
% 1.91/0.95  fd_pseudo_cond                          2
% 1.91/0.95  AC symbols                              0
% 1.91/0.95  
% 1.91/0.95  ------ Schedule dynamic 5 is on 
% 1.91/0.95  
% 1.91/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  ------ 
% 1.91/0.95  Current options:
% 1.91/0.95  ------ 
% 1.91/0.95  
% 1.91/0.95  ------ Input Options
% 1.91/0.95  
% 1.91/0.95  --out_options                           all
% 1.91/0.95  --tptp_safe_out                         true
% 1.91/0.95  --problem_path                          ""
% 1.91/0.95  --include_path                          ""
% 1.91/0.95  --clausifier                            res/vclausify_rel
% 1.91/0.95  --clausifier_options                    --mode clausify
% 1.91/0.95  --stdin                                 false
% 1.91/0.95  --stats_out                             all
% 1.91/0.95  
% 1.91/0.95  ------ General Options
% 1.91/0.95  
% 1.91/0.95  --fof                                   false
% 1.91/0.95  --time_out_real                         305.
% 1.91/0.95  --time_out_virtual                      -1.
% 1.91/0.95  --symbol_type_check                     false
% 1.91/0.95  --clausify_out                          false
% 1.91/0.95  --sig_cnt_out                           false
% 1.91/0.95  --trig_cnt_out                          false
% 1.91/0.95  --trig_cnt_out_tolerance                1.
% 1.91/0.95  --trig_cnt_out_sk_spl                   false
% 1.91/0.95  --abstr_cl_out                          false
% 1.91/0.95  
% 1.91/0.95  ------ Global Options
% 1.91/0.95  
% 1.91/0.95  --schedule                              default
% 1.91/0.95  --add_important_lit                     false
% 1.91/0.95  --prop_solver_per_cl                    1000
% 1.91/0.95  --min_unsat_core                        false
% 1.91/0.95  --soft_assumptions                      false
% 1.91/0.95  --soft_lemma_size                       3
% 1.91/0.95  --prop_impl_unit_size                   0
% 1.91/0.95  --prop_impl_unit                        []
% 1.91/0.95  --share_sel_clauses                     true
% 1.91/0.95  --reset_solvers                         false
% 1.91/0.95  --bc_imp_inh                            [conj_cone]
% 1.91/0.95  --conj_cone_tolerance                   3.
% 1.91/0.95  --extra_neg_conj                        none
% 1.91/0.95  --large_theory_mode                     true
% 1.91/0.95  --prolific_symb_bound                   200
% 1.91/0.95  --lt_threshold                          2000
% 1.91/0.95  --clause_weak_htbl                      true
% 1.91/0.95  --gc_record_bc_elim                     false
% 1.91/0.95  
% 1.91/0.95  ------ Preprocessing Options
% 1.91/0.95  
% 1.91/0.95  --preprocessing_flag                    true
% 1.91/0.95  --time_out_prep_mult                    0.1
% 1.91/0.95  --splitting_mode                        input
% 1.91/0.95  --splitting_grd                         true
% 1.91/0.95  --splitting_cvd                         false
% 1.91/0.95  --splitting_cvd_svl                     false
% 1.91/0.95  --splitting_nvd                         32
% 1.91/0.95  --sub_typing                            true
% 1.91/0.95  --prep_gs_sim                           true
% 1.91/0.95  --prep_unflatten                        true
% 1.91/0.95  --prep_res_sim                          true
% 1.91/0.95  --prep_upred                            true
% 1.91/0.95  --prep_sem_filter                       exhaustive
% 1.91/0.95  --prep_sem_filter_out                   false
% 1.91/0.95  --pred_elim                             true
% 1.91/0.95  --res_sim_input                         true
% 1.91/0.95  --eq_ax_congr_red                       true
% 1.91/0.95  --pure_diseq_elim                       true
% 1.91/0.95  --brand_transform                       false
% 1.91/0.95  --non_eq_to_eq                          false
% 1.91/0.95  --prep_def_merge                        true
% 1.91/0.95  --prep_def_merge_prop_impl              false
% 1.91/0.95  --prep_def_merge_mbd                    true
% 1.91/0.95  --prep_def_merge_tr_red                 false
% 1.91/0.95  --prep_def_merge_tr_cl                  false
% 1.91/0.95  --smt_preprocessing                     true
% 1.91/0.95  --smt_ac_axioms                         fast
% 1.91/0.95  --preprocessed_out                      false
% 1.91/0.95  --preprocessed_stats                    false
% 1.91/0.95  
% 1.91/0.95  ------ Abstraction refinement Options
% 1.91/0.95  
% 1.91/0.95  --abstr_ref                             []
% 1.91/0.95  --abstr_ref_prep                        false
% 1.91/0.95  --abstr_ref_until_sat                   false
% 1.91/0.95  --abstr_ref_sig_restrict                funpre
% 1.91/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/0.95  --abstr_ref_under                       []
% 1.91/0.95  
% 1.91/0.95  ------ SAT Options
% 1.91/0.95  
% 1.91/0.95  --sat_mode                              false
% 1.91/0.95  --sat_fm_restart_options                ""
% 1.91/0.95  --sat_gr_def                            false
% 1.91/0.95  --sat_epr_types                         true
% 1.91/0.95  --sat_non_cyclic_types                  false
% 1.91/0.95  --sat_finite_models                     false
% 1.91/0.95  --sat_fm_lemmas                         false
% 1.91/0.95  --sat_fm_prep                           false
% 1.91/0.95  --sat_fm_uc_incr                        true
% 1.91/0.95  --sat_out_model                         small
% 1.91/0.95  --sat_out_clauses                       false
% 1.91/0.95  
% 1.91/0.95  ------ QBF Options
% 1.91/0.95  
% 1.91/0.95  --qbf_mode                              false
% 1.91/0.95  --qbf_elim_univ                         false
% 1.91/0.95  --qbf_dom_inst                          none
% 1.91/0.95  --qbf_dom_pre_inst                      false
% 1.91/0.95  --qbf_sk_in                             false
% 1.91/0.95  --qbf_pred_elim                         true
% 1.91/0.95  --qbf_split                             512
% 1.91/0.95  
% 1.91/0.95  ------ BMC1 Options
% 1.91/0.95  
% 1.91/0.95  --bmc1_incremental                      false
% 1.91/0.95  --bmc1_axioms                           reachable_all
% 1.91/0.95  --bmc1_min_bound                        0
% 1.91/0.95  --bmc1_max_bound                        -1
% 1.91/0.95  --bmc1_max_bound_default                -1
% 1.91/0.95  --bmc1_symbol_reachability              true
% 1.91/0.95  --bmc1_property_lemmas                  false
% 1.91/0.95  --bmc1_k_induction                      false
% 1.91/0.95  --bmc1_non_equiv_states                 false
% 1.91/0.95  --bmc1_deadlock                         false
% 1.91/0.95  --bmc1_ucm                              false
% 1.91/0.95  --bmc1_add_unsat_core                   none
% 1.91/0.95  --bmc1_unsat_core_children              false
% 1.91/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/0.95  --bmc1_out_stat                         full
% 1.91/0.95  --bmc1_ground_init                      false
% 1.91/0.95  --bmc1_pre_inst_next_state              false
% 1.91/0.95  --bmc1_pre_inst_state                   false
% 1.91/0.95  --bmc1_pre_inst_reach_state             false
% 1.91/0.95  --bmc1_out_unsat_core                   false
% 1.91/0.95  --bmc1_aig_witness_out                  false
% 1.91/0.95  --bmc1_verbose                          false
% 1.91/0.95  --bmc1_dump_clauses_tptp                false
% 1.91/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.91/0.95  --bmc1_dump_file                        -
% 1.91/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.91/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.91/0.95  --bmc1_ucm_extend_mode                  1
% 1.91/0.95  --bmc1_ucm_init_mode                    2
% 1.91/0.95  --bmc1_ucm_cone_mode                    none
% 1.91/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.91/0.95  --bmc1_ucm_relax_model                  4
% 1.91/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.91/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/0.95  --bmc1_ucm_layered_model                none
% 1.91/0.95  --bmc1_ucm_max_lemma_size               10
% 1.91/0.95  
% 1.91/0.95  ------ AIG Options
% 1.91/0.95  
% 1.91/0.95  --aig_mode                              false
% 1.91/0.95  
% 1.91/0.95  ------ Instantiation Options
% 1.91/0.95  
% 1.91/0.95  --instantiation_flag                    true
% 1.91/0.95  --inst_sos_flag                         false
% 1.91/0.95  --inst_sos_phase                        true
% 1.91/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/0.95  --inst_lit_sel_side                     none
% 1.91/0.95  --inst_solver_per_active                1400
% 1.91/0.95  --inst_solver_calls_frac                1.
% 1.91/0.95  --inst_passive_queue_type               priority_queues
% 1.91/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/0.95  --inst_passive_queues_freq              [25;2]
% 1.91/0.95  --inst_dismatching                      true
% 1.91/0.95  --inst_eager_unprocessed_to_passive     true
% 1.91/0.95  --inst_prop_sim_given                   true
% 1.91/0.95  --inst_prop_sim_new                     false
% 1.91/0.95  --inst_subs_new                         false
% 1.91/0.95  --inst_eq_res_simp                      false
% 1.91/0.95  --inst_subs_given                       false
% 1.91/0.95  --inst_orphan_elimination               true
% 1.91/0.95  --inst_learning_loop_flag               true
% 1.91/0.95  --inst_learning_start                   3000
% 1.91/0.95  --inst_learning_factor                  2
% 1.91/0.95  --inst_start_prop_sim_after_learn       3
% 1.91/0.95  --inst_sel_renew                        solver
% 1.91/0.95  --inst_lit_activity_flag                true
% 1.91/0.95  --inst_restr_to_given                   false
% 1.91/0.95  --inst_activity_threshold               500
% 1.91/0.95  --inst_out_proof                        true
% 1.91/0.95  
% 1.91/0.95  ------ Resolution Options
% 1.91/0.95  
% 1.91/0.95  --resolution_flag                       false
% 1.91/0.95  --res_lit_sel                           adaptive
% 1.91/0.95  --res_lit_sel_side                      none
% 1.91/0.95  --res_ordering                          kbo
% 1.91/0.95  --res_to_prop_solver                    active
% 1.91/0.95  --res_prop_simpl_new                    false
% 1.91/0.95  --res_prop_simpl_given                  true
% 1.91/0.95  --res_passive_queue_type                priority_queues
% 1.91/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/0.95  --res_passive_queues_freq               [15;5]
% 1.91/0.95  --res_forward_subs                      full
% 1.91/0.95  --res_backward_subs                     full
% 1.91/0.95  --res_forward_subs_resolution           true
% 1.91/0.95  --res_backward_subs_resolution          true
% 1.91/0.95  --res_orphan_elimination                true
% 1.91/0.95  --res_time_limit                        2.
% 1.91/0.95  --res_out_proof                         true
% 1.91/0.95  
% 1.91/0.95  ------ Superposition Options
% 1.91/0.95  
% 1.91/0.95  --superposition_flag                    true
% 1.91/0.95  --sup_passive_queue_type                priority_queues
% 1.91/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.91/0.95  --demod_completeness_check              fast
% 1.91/0.95  --demod_use_ground                      true
% 1.91/0.95  --sup_to_prop_solver                    passive
% 1.91/0.95  --sup_prop_simpl_new                    true
% 1.91/0.95  --sup_prop_simpl_given                  true
% 1.91/0.95  --sup_fun_splitting                     false
% 1.91/0.95  --sup_smt_interval                      50000
% 1.91/0.95  
% 1.91/0.95  ------ Superposition Simplification Setup
% 1.91/0.95  
% 1.91/0.95  --sup_indices_passive                   []
% 1.91/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.95  --sup_full_bw                           [BwDemod]
% 1.91/0.95  --sup_immed_triv                        [TrivRules]
% 1.91/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.95  --sup_immed_bw_main                     []
% 1.91/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.95  
% 1.91/0.95  ------ Combination Options
% 1.91/0.95  
% 1.91/0.95  --comb_res_mult                         3
% 1.91/0.95  --comb_sup_mult                         2
% 1.91/0.95  --comb_inst_mult                        10
% 1.91/0.95  
% 1.91/0.95  ------ Debug Options
% 1.91/0.95  
% 1.91/0.95  --dbg_backtrace                         false
% 1.91/0.95  --dbg_dump_prop_clauses                 false
% 1.91/0.95  --dbg_dump_prop_clauses_file            -
% 1.91/0.95  --dbg_out_stat                          false
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  ------ Proving...
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  % SZS status Theorem for theBenchmark.p
% 1.91/0.95  
% 1.91/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.91/0.95  
% 1.91/0.95  fof(f7,axiom,(
% 1.91/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r7_relat_2(X0,X1) <=> ! [X2,X3] : ~(~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f23,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : (r7_relat_2(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 1.91/0.95    inference(ennf_transformation,[],[f7])).
% 1.91/0.95  
% 1.91/0.95  fof(f40,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : ((r7_relat_2(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r7_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.91/0.95    inference(nnf_transformation,[],[f23])).
% 1.91/0.95  
% 1.91/0.95  fof(f41,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : ((r7_relat_2(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r7_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.91/0.95    inference(rectify,[],[f40])).
% 1.91/0.95  
% 1.91/0.95  fof(f42,plain,(
% 1.91/0.95    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) & ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1)))),
% 1.91/0.95    introduced(choice_axiom,[])).
% 1.91/0.95  
% 1.91/0.95  fof(f43,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : ((r7_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) & ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r7_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.91/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f42])).
% 1.91/0.95  
% 1.91/0.95  fof(f60,plain,(
% 1.91/0.95    ( ! [X0,X1] : (r7_relat_2(X0,X1) | r2_hidden(sK2(X0,X1),X1) | ~v1_relat_1(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f43])).
% 1.91/0.95  
% 1.91/0.95  fof(f1,axiom,(
% 1.91/0.95    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f35,plain,(
% 1.91/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.91/0.95    inference(nnf_transformation,[],[f1])).
% 1.91/0.95  
% 1.91/0.95  fof(f36,plain,(
% 1.91/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.91/0.95    inference(rectify,[],[f35])).
% 1.91/0.95  
% 1.91/0.95  fof(f37,plain,(
% 1.91/0.95    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 1.91/0.95    introduced(choice_axiom,[])).
% 1.91/0.95  
% 1.91/0.95  fof(f38,plain,(
% 1.91/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.91/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 1.91/0.95  
% 1.91/0.95  fof(f48,plain,(
% 1.91/0.95    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.91/0.95    inference(cnf_transformation,[],[f38])).
% 1.91/0.95  
% 1.91/0.95  fof(f77,plain,(
% 1.91/0.95    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.91/0.95    inference(equality_resolution,[],[f48])).
% 1.91/0.95  
% 1.91/0.95  fof(f14,conjecture,(
% 1.91/0.95    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f15,negated_conjecture,(
% 1.91/0.95    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.91/0.95    inference(negated_conjecture,[],[f14])).
% 1.91/0.95  
% 1.91/0.95  fof(f33,plain,(
% 1.91/0.95    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.91/0.95    inference(ennf_transformation,[],[f15])).
% 1.91/0.95  
% 1.91/0.95  fof(f34,plain,(
% 1.91/0.95    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.91/0.95    inference(flattening,[],[f33])).
% 1.91/0.95  
% 1.91/0.95  fof(f46,plain,(
% 1.91/0.95    ( ! [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),sK4),X0)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.91/0.95    introduced(choice_axiom,[])).
% 1.91/0.95  
% 1.91/0.95  fof(f45,plain,(
% 1.91/0.95    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),X1),sK3)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.91/0.95    introduced(choice_axiom,[])).
% 1.91/0.95  
% 1.91/0.95  fof(f47,plain,(
% 1.91/0.95    ((~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.91/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f46,f45])).
% 1.91/0.95  
% 1.91/0.95  fof(f73,plain,(
% 1.91/0.95    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.91/0.95    inference(cnf_transformation,[],[f47])).
% 1.91/0.95  
% 1.91/0.95  fof(f12,axiom,(
% 1.91/0.95    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f29,plain,(
% 1.91/0.95    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.91/0.95    inference(ennf_transformation,[],[f12])).
% 1.91/0.95  
% 1.91/0.95  fof(f30,plain,(
% 1.91/0.95    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.91/0.95    inference(flattening,[],[f29])).
% 1.91/0.95  
% 1.91/0.95  fof(f68,plain,(
% 1.91/0.95    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f30])).
% 1.91/0.95  
% 1.91/0.95  fof(f10,axiom,(
% 1.91/0.95    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f27,plain,(
% 1.91/0.95    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.91/0.95    inference(ennf_transformation,[],[f10])).
% 1.91/0.95  
% 1.91/0.95  fof(f66,plain,(
% 1.91/0.95    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f27])).
% 1.91/0.95  
% 1.91/0.95  fof(f5,axiom,(
% 1.91/0.95    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f20,plain,(
% 1.91/0.95    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.91/0.95    inference(ennf_transformation,[],[f5])).
% 1.91/0.95  
% 1.91/0.95  fof(f21,plain,(
% 1.91/0.95    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.91/0.95    inference(flattening,[],[f20])).
% 1.91/0.95  
% 1.91/0.95  fof(f55,plain,(
% 1.91/0.95    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f21])).
% 1.91/0.95  
% 1.91/0.95  fof(f70,plain,(
% 1.91/0.95    ~v2_struct_0(sK3)),
% 1.91/0.95    inference(cnf_transformation,[],[f47])).
% 1.91/0.95  
% 1.91/0.95  fof(f72,plain,(
% 1.91/0.95    l1_orders_2(sK3)),
% 1.91/0.95    inference(cnf_transformation,[],[f47])).
% 1.91/0.95  
% 1.91/0.95  fof(f6,axiom,(
% 1.91/0.95    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f22,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.91/0.95    inference(ennf_transformation,[],[f6])).
% 1.91/0.95  
% 1.91/0.95  fof(f39,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : (((v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1)) & (r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.91/0.95    inference(nnf_transformation,[],[f22])).
% 1.91/0.95  
% 1.91/0.95  fof(f57,plain,(
% 1.91/0.95    ( ! [X0,X1] : (v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f39])).
% 1.91/0.95  
% 1.91/0.95  fof(f74,plain,(
% 1.91/0.95    ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)),
% 1.91/0.95    inference(cnf_transformation,[],[f47])).
% 1.91/0.95  
% 1.91/0.95  fof(f9,axiom,(
% 1.91/0.95    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f25,plain,(
% 1.91/0.95    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.91/0.95    inference(ennf_transformation,[],[f9])).
% 1.91/0.95  
% 1.91/0.95  fof(f26,plain,(
% 1.91/0.95    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.91/0.95    inference(flattening,[],[f25])).
% 1.91/0.95  
% 1.91/0.95  fof(f65,plain,(
% 1.91/0.95    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f26])).
% 1.91/0.95  
% 1.91/0.95  fof(f11,axiom,(
% 1.91/0.95    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f28,plain,(
% 1.91/0.95    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.91/0.95    inference(ennf_transformation,[],[f11])).
% 1.91/0.95  
% 1.91/0.95  fof(f67,plain,(
% 1.91/0.95    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f28])).
% 1.91/0.95  
% 1.91/0.95  fof(f4,axiom,(
% 1.91/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f19,plain,(
% 1.91/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.95    inference(ennf_transformation,[],[f4])).
% 1.91/0.95  
% 1.91/0.95  fof(f54,plain,(
% 1.91/0.95    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/0.95    inference(cnf_transformation,[],[f19])).
% 1.91/0.95  
% 1.91/0.95  fof(f59,plain,(
% 1.91/0.95    ( ! [X0,X1] : (r7_relat_2(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_relat_1(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f43])).
% 1.91/0.95  
% 1.91/0.95  fof(f61,plain,(
% 1.91/0.95    ( ! [X0,X1] : (r7_relat_2(X0,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f43])).
% 1.91/0.95  
% 1.91/0.95  fof(f13,axiom,(
% 1.91/0.95    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f31,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.91/0.95    inference(ennf_transformation,[],[f13])).
% 1.91/0.95  
% 1.91/0.95  fof(f32,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.91/0.95    inference(flattening,[],[f31])).
% 1.91/0.95  
% 1.91/0.95  fof(f69,plain,(
% 1.91/0.95    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f32])).
% 1.91/0.95  
% 1.91/0.95  fof(f71,plain,(
% 1.91/0.95    v3_orders_2(sK3)),
% 1.91/0.95    inference(cnf_transformation,[],[f47])).
% 1.91/0.95  
% 1.91/0.95  fof(f8,axiom,(
% 1.91/0.95    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 1.91/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.95  
% 1.91/0.95  fof(f24,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.91/0.95    inference(ennf_transformation,[],[f8])).
% 1.91/0.95  
% 1.91/0.95  fof(f44,plain,(
% 1.91/0.95    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.91/0.95    inference(nnf_transformation,[],[f24])).
% 1.91/0.95  
% 1.91/0.95  fof(f63,plain,(
% 1.91/0.95    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.91/0.95    inference(cnf_transformation,[],[f44])).
% 1.91/0.95  
% 1.91/0.95  cnf(c_12,plain,
% 1.91/0.95      ( r7_relat_2(X0,X1) | r2_hidden(sK2(X0,X1),X1) | ~ v1_relat_1(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f60]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1496,plain,
% 1.91/0.95      ( r7_relat_2(X0,X1) = iProver_top
% 1.91/0.95      | r2_hidden(sK2(X0,X1),X1) = iProver_top
% 1.91/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3,plain,
% 1.91/0.95      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 1.91/0.95      inference(cnf_transformation,[],[f77]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1501,plain,
% 1.91/0.95      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_2802,plain,
% 1.91/0.95      ( sK2(X0,k1_tarski(X1)) = X1
% 1.91/0.95      | r7_relat_2(X0,k1_tarski(X1)) = iProver_top
% 1.91/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.91/0.95      inference(superposition,[status(thm)],[c_1496,c_1501]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_23,negated_conjecture,
% 1.91/0.95      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.91/0.95      inference(cnf_transformation,[],[f73]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1493,plain,
% 1.91/0.95      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_20,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,X1)
% 1.91/0.95      | v1_xboole_0(X1)
% 1.91/0.95      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f68]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_18,plain,
% 1.91/0.95      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f66]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_7,plain,
% 1.91/0.95      ( v2_struct_0(X0)
% 1.91/0.95      | ~ l1_struct_0(X0)
% 1.91/0.95      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.91/0.95      inference(cnf_transformation,[],[f55]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_309,plain,
% 1.91/0.95      ( ~ l1_orders_2(X0)
% 1.91/0.95      | v2_struct_0(X0)
% 1.91/0.95      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.91/0.95      inference(resolution,[status(thm)],[c_18,c_7]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_26,negated_conjecture,
% 1.91/0.95      ( ~ v2_struct_0(sK3) ),
% 1.91/0.95      inference(cnf_transformation,[],[f70]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_348,plain,
% 1.91/0.95      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.91/0.95      inference(resolution_lifted,[status(thm)],[c_309,c_26]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_349,plain,
% 1.91/0.95      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.91/0.95      inference(unflattening,[status(thm)],[c_348]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_24,negated_conjecture,
% 1.91/0.95      ( l1_orders_2(sK3) ),
% 1.91/0.95      inference(cnf_transformation,[],[f72]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_42,plain,
% 1.91/0.95      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 1.91/0.95      inference(instantiation,[status(thm)],[c_18]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_75,plain,
% 1.91/0.95      ( v2_struct_0(sK3)
% 1.91/0.95      | ~ l1_struct_0(sK3)
% 1.91/0.95      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.91/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_351,plain,
% 1.91/0.95      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.91/0.95      inference(global_propositional_subsumption,
% 1.91/0.95                [status(thm)],
% 1.91/0.95                [c_349,c_26,c_24,c_42,c_75]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_361,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,X1)
% 1.91/0.95      | k6_domain_1(X1,X0) = k1_tarski(X0)
% 1.91/0.95      | u1_struct_0(sK3) != X1 ),
% 1.91/0.95      inference(resolution_lifted,[status(thm)],[c_20,c_351]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_362,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.91/0.95      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 1.91/0.95      inference(unflattening,[status(thm)],[c_361]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1492,plain,
% 1.91/0.95      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 1.91/0.95      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1685,plain,
% 1.91/0.95      ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) ),
% 1.91/0.95      inference(superposition,[status(thm)],[c_1493,c_1492]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_8,plain,
% 1.91/0.95      ( ~ r7_relat_2(u1_orders_2(X0),X1)
% 1.91/0.95      | v6_orders_2(X1,X0)
% 1.91/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.91/0.95      | ~ l1_orders_2(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f57]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_22,negated_conjecture,
% 1.91/0.95      ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)
% 1.91/0.95      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.91/0.95      inference(cnf_transformation,[],[f74]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_407,plain,
% 1.91/0.95      ( ~ r7_relat_2(u1_orders_2(X0),X1)
% 1.91/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.91/0.95      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.91/0.95      | ~ l1_orders_2(X0)
% 1.91/0.95      | k6_domain_1(u1_struct_0(sK3),sK4) != X1
% 1.91/0.95      | sK3 != X0 ),
% 1.91/0.95      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_408,plain,
% 1.91/0.95      ( ~ r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4))
% 1.91/0.95      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.91/0.95      | ~ l1_orders_2(sK3) ),
% 1.91/0.95      inference(unflattening,[status(thm)],[c_407]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_410,plain,
% 1.91/0.95      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.91/0.95      | ~ r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) ),
% 1.91/0.95      inference(global_propositional_subsumption,
% 1.91/0.95                [status(thm)],
% 1.91/0.95                [c_408,c_24]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_411,plain,
% 1.91/0.95      ( ~ r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4))
% 1.91/0.95      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.91/0.95      inference(renaming,[status(thm)],[c_410]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1489,plain,
% 1.91/0.95      ( r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
% 1.91/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_29,plain,
% 1.91/0.95      ( l1_orders_2(sK3) = iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_30,plain,
% 1.91/0.95      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_409,plain,
% 1.91/0.95      ( r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
% 1.91/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.91/0.95      | l1_orders_2(sK3) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_17,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,X1)
% 1.91/0.95      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.91/0.95      | v1_xboole_0(X1) ),
% 1.91/0.95      inference(cnf_transformation,[],[f65]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_373,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,X1)
% 1.91/0.95      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.91/0.95      | u1_struct_0(sK3) != X1 ),
% 1.91/0.95      inference(resolution_lifted,[status(thm)],[c_17,c_351]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_374,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.91/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.91/0.95      inference(unflattening,[status(thm)],[c_373]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1630,plain,
% 1.91/0.95      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.91/0.95      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.91/0.95      inference(instantiation,[status(thm)],[c_374]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1631,plain,
% 1.91/0.95      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 1.91/0.95      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_1630]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1665,plain,
% 1.91/0.95      ( r7_relat_2(u1_orders_2(sK3),k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
% 1.91/0.95      inference(global_propositional_subsumption,
% 1.91/0.95                [status(thm)],
% 1.91/0.95                [c_1489,c_29,c_30,c_409,c_1631]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1813,plain,
% 1.91/0.95      ( r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4)) != iProver_top ),
% 1.91/0.95      inference(demodulation,[status(thm)],[c_1685,c_1665]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3341,plain,
% 1.91/0.95      ( sK2(u1_orders_2(sK3),k1_tarski(sK4)) = sK4
% 1.91/0.95      | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
% 1.91/0.95      inference(superposition,[status(thm)],[c_2802,c_1813]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_19,plain,
% 1.91/0.95      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.91/0.95      | ~ l1_orders_2(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f67]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_38,plain,
% 1.91/0.95      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 1.91/0.95      | l1_orders_2(X0) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_40,plain,
% 1.91/0.95      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
% 1.91/0.95      | l1_orders_2(sK3) != iProver_top ),
% 1.91/0.95      inference(instantiation,[status(thm)],[c_38]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_6,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/0.95      | v1_relat_1(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f54]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1642,plain,
% 1.91/0.95      ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
% 1.91/0.95      | v1_relat_1(u1_orders_2(sK3)) ),
% 1.91/0.95      inference(instantiation,[status(thm)],[c_6]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1643,plain,
% 1.91/0.95      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 1.91/0.95      | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3438,plain,
% 1.91/0.95      ( sK2(u1_orders_2(sK3),k1_tarski(sK4)) = sK4 ),
% 1.91/0.95      inference(global_propositional_subsumption,
% 1.91/0.95                [status(thm)],
% 1.91/0.95                [c_3341,c_29,c_40,c_1643]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_13,plain,
% 1.91/0.95      ( r7_relat_2(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~ v1_relat_1(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f59]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1495,plain,
% 1.91/0.95      ( r7_relat_2(X0,X1) = iProver_top
% 1.91/0.95      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 1.91/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_2778,plain,
% 1.91/0.95      ( sK1(X0,k1_tarski(X1)) = X1
% 1.91/0.95      | r7_relat_2(X0,k1_tarski(X1)) = iProver_top
% 1.91/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.91/0.95      inference(superposition,[status(thm)],[c_1495,c_1501]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3164,plain,
% 1.91/0.95      ( sK1(u1_orders_2(sK3),k1_tarski(sK4)) = sK4
% 1.91/0.95      | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
% 1.91/0.95      inference(superposition,[status(thm)],[c_2778,c_1813]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3233,plain,
% 1.91/0.95      ( sK1(u1_orders_2(sK3),k1_tarski(sK4)) = sK4 ),
% 1.91/0.95      inference(global_propositional_subsumption,
% 1.91/0.95                [status(thm)],
% 1.91/0.95                [c_3164,c_29,c_40,c_1643]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_11,plain,
% 1.91/0.95      ( r7_relat_2(X0,X1)
% 1.91/0.95      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 1.91/0.95      | ~ v1_relat_1(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f61]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1497,plain,
% 1.91/0.95      ( r7_relat_2(X0,X1) = iProver_top
% 1.91/0.95      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) != iProver_top
% 1.91/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3238,plain,
% 1.91/0.95      ( r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4)) = iProver_top
% 1.91/0.95      | r2_hidden(k4_tarski(sK4,sK2(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3)) != iProver_top
% 1.91/0.95      | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
% 1.91/0.95      inference(superposition,[status(thm)],[c_3233,c_1497]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3331,plain,
% 1.91/0.95      ( r2_hidden(k4_tarski(sK4,sK2(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3)) != iProver_top ),
% 1.91/0.95      inference(global_propositional_subsumption,
% 1.91/0.95                [status(thm)],
% 1.91/0.95                [c_3238,c_29,c_40,c_1643,c_1813]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_3441,plain,
% 1.91/0.95      ( r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) != iProver_top ),
% 1.91/0.95      inference(demodulation,[status(thm)],[c_3438,c_3331]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_21,plain,
% 1.91/0.95      ( r1_orders_2(X0,X1,X1)
% 1.91/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.95      | ~ v3_orders_2(X0)
% 1.91/0.95      | ~ l1_orders_2(X0)
% 1.91/0.95      | v2_struct_0(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f69]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_25,negated_conjecture,
% 1.91/0.95      ( v3_orders_2(sK3) ),
% 1.91/0.95      inference(cnf_transformation,[],[f71]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_327,plain,
% 1.91/0.95      ( r1_orders_2(X0,X1,X1)
% 1.91/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.95      | ~ l1_orders_2(X0)
% 1.91/0.95      | v2_struct_0(X0)
% 1.91/0.95      | sK3 != X0 ),
% 1.91/0.95      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_328,plain,
% 1.91/0.95      ( r1_orders_2(sK3,X0,X0)
% 1.91/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.91/0.95      | ~ l1_orders_2(sK3)
% 1.91/0.95      | v2_struct_0(sK3) ),
% 1.91/0.95      inference(unflattening,[status(thm)],[c_327]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_332,plain,
% 1.91/0.95      ( r1_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.91/0.95      inference(global_propositional_subsumption,
% 1.91/0.95                [status(thm)],
% 1.91/0.95                [c_328,c_26,c_24]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_16,plain,
% 1.91/0.95      ( ~ r1_orders_2(X0,X1,X2)
% 1.91/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.95      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.91/0.95      | ~ l1_orders_2(X0) ),
% 1.91/0.95      inference(cnf_transformation,[],[f63]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_431,plain,
% 1.91/0.95      ( ~ r1_orders_2(X0,X1,X2)
% 1.91/0.95      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.95      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.95      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.91/0.95      | sK3 != X0 ),
% 1.91/0.95      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_432,plain,
% 1.91/0.95      ( ~ r1_orders_2(sK3,X0,X1)
% 1.91/0.95      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.91/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.91/0.95      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
% 1.91/0.95      inference(unflattening,[status(thm)],[c_431]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_478,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.91/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.91/0.95      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.91/0.95      | r2_hidden(k4_tarski(X0,X2),u1_orders_2(sK3))
% 1.91/0.95      | X2 != X1
% 1.91/0.95      | X0 != X1
% 1.91/0.95      | sK3 != sK3 ),
% 1.91/0.95      inference(resolution_lifted,[status(thm)],[c_332,c_432]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_479,plain,
% 1.91/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.91/0.95      | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK3)) ),
% 1.91/0.95      inference(unflattening,[status(thm)],[c_478]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1639,plain,
% 1.91/0.95      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.91/0.95      | r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) ),
% 1.91/0.95      inference(instantiation,[status(thm)],[c_479]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(c_1640,plain,
% 1.91/0.95      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.91/0.95      | r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) = iProver_top ),
% 1.91/0.95      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 1.91/0.95  
% 1.91/0.95  cnf(contradiction,plain,
% 1.91/0.95      ( $false ),
% 1.91/0.95      inference(minisat,[status(thm)],[c_3441,c_1640,c_30]) ).
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 1.91/0.95  
% 1.91/0.95  ------                               Statistics
% 1.91/0.95  
% 1.91/0.95  ------ General
% 1.91/0.95  
% 1.91/0.95  abstr_ref_over_cycles:                  0
% 1.91/0.95  abstr_ref_under_cycles:                 0
% 1.91/0.95  gc_basic_clause_elim:                   0
% 1.91/0.95  forced_gc_time:                         0
% 1.91/0.95  parsing_time:                           0.01
% 1.91/0.95  unif_index_cands_time:                  0.
% 1.91/0.95  unif_index_add_time:                    0.
% 1.91/0.95  orderings_time:                         0.
% 1.91/0.95  out_proof_time:                         0.008
% 1.91/0.95  total_time:                             0.122
% 1.91/0.95  num_of_symbols:                         54
% 1.91/0.95  num_of_terms:                           3024
% 1.91/0.95  
% 1.91/0.95  ------ Preprocessing
% 1.91/0.95  
% 1.91/0.95  num_of_splits:                          0
% 1.91/0.95  num_of_split_atoms:                     0
% 1.91/0.95  num_of_reused_defs:                     0
% 1.91/0.95  num_eq_ax_congr_red:                    30
% 1.91/0.95  num_of_sem_filtered_clauses:            1
% 1.91/0.95  num_of_subtypes:                        0
% 1.91/0.95  monotx_restored_types:                  0
% 1.91/0.95  sat_num_of_epr_types:                   0
% 1.91/0.95  sat_num_of_non_cyclic_types:            0
% 1.91/0.95  sat_guarded_non_collapsed_types:        0
% 1.91/0.95  num_pure_diseq_elim:                    0
% 1.91/0.95  simp_replaced_by:                       0
% 1.91/0.95  res_preprocessed:                       104
% 1.91/0.95  prep_upred:                             0
% 1.91/0.95  prep_unflattend:                        28
% 1.91/0.95  smt_new_axioms:                         0
% 1.91/0.95  pred_elim_cands:                        4
% 1.91/0.95  pred_elim:                              7
% 1.91/0.95  pred_elim_cl:                           9
% 1.91/0.95  pred_elim_cycles:                       11
% 1.91/0.95  merged_defs:                            0
% 1.91/0.95  merged_defs_ncl:                        0
% 1.91/0.95  bin_hyper_res:                          0
% 1.91/0.95  prep_cycles:                            4
% 1.91/0.95  pred_elim_time:                         0.012
% 1.91/0.95  splitting_time:                         0.
% 1.91/0.95  sem_filter_time:                        0.
% 1.91/0.95  monotx_time:                            0.001
% 1.91/0.95  subtype_inf_time:                       0.
% 1.91/0.95  
% 1.91/0.95  ------ Problem properties
% 1.91/0.95  
% 1.91/0.95  clauses:                                18
% 1.91/0.95  conjectures:                            1
% 1.91/0.95  epr:                                    0
% 1.91/0.95  horn:                                   14
% 1.91/0.95  ground:                                 3
% 1.91/0.95  unary:                                  3
% 1.91/0.95  binary:                                 8
% 1.91/0.95  lits:                                   43
% 1.91/0.95  lits_eq:                                6
% 1.91/0.95  fd_pure:                                0
% 1.91/0.95  fd_pseudo:                              0
% 1.91/0.95  fd_cond:                                0
% 1.91/0.95  fd_pseudo_cond:                         2
% 1.91/0.95  ac_symbols:                             0
% 1.91/0.95  
% 1.91/0.95  ------ Propositional Solver
% 1.91/0.95  
% 1.91/0.95  prop_solver_calls:                      26
% 1.91/0.95  prop_fast_solver_calls:                 760
% 1.91/0.95  smt_solver_calls:                       0
% 1.91/0.95  smt_fast_solver_calls:                  0
% 1.91/0.95  prop_num_of_clauses:                    1097
% 1.91/0.95  prop_preprocess_simplified:             4461
% 1.91/0.95  prop_fo_subsumed:                       12
% 1.91/0.95  prop_solver_time:                       0.
% 1.91/0.95  smt_solver_time:                        0.
% 1.91/0.95  smt_fast_solver_time:                   0.
% 1.91/0.95  prop_fast_solver_time:                  0.
% 1.91/0.95  prop_unsat_core_time:                   0.
% 1.91/0.95  
% 1.91/0.95  ------ QBF
% 1.91/0.95  
% 1.91/0.95  qbf_q_res:                              0
% 1.91/0.95  qbf_num_tautologies:                    0
% 1.91/0.95  qbf_prep_cycles:                        0
% 1.91/0.95  
% 1.91/0.95  ------ BMC1
% 1.91/0.95  
% 1.91/0.95  bmc1_current_bound:                     -1
% 1.91/0.95  bmc1_last_solved_bound:                 -1
% 1.91/0.95  bmc1_unsat_core_size:                   -1
% 1.91/0.95  bmc1_unsat_core_parents_size:           -1
% 1.91/0.95  bmc1_merge_next_fun:                    0
% 1.91/0.95  bmc1_unsat_core_clauses_time:           0.
% 1.91/0.95  
% 1.91/0.95  ------ Instantiation
% 1.91/0.95  
% 1.91/0.95  inst_num_of_clauses:                    319
% 1.91/0.95  inst_num_in_passive:                    96
% 1.91/0.95  inst_num_in_active:                     158
% 1.91/0.95  inst_num_in_unprocessed:                65
% 1.91/0.95  inst_num_of_loops:                      170
% 1.91/0.95  inst_num_of_learning_restarts:          0
% 1.91/0.95  inst_num_moves_active_passive:          10
% 1.91/0.95  inst_lit_activity:                      0
% 1.91/0.95  inst_lit_activity_moves:                0
% 1.91/0.95  inst_num_tautologies:                   0
% 1.91/0.95  inst_num_prop_implied:                  0
% 1.91/0.95  inst_num_existing_simplified:           0
% 1.91/0.95  inst_num_eq_res_simplified:             0
% 1.91/0.95  inst_num_child_elim:                    0
% 1.91/0.95  inst_num_of_dismatching_blockings:      74
% 1.91/0.95  inst_num_of_non_proper_insts:           262
% 1.91/0.95  inst_num_of_duplicates:                 0
% 1.91/0.95  inst_inst_num_from_inst_to_res:         0
% 1.91/0.95  inst_dismatching_checking_time:         0.
% 1.91/0.95  
% 1.91/0.95  ------ Resolution
% 1.91/0.95  
% 1.91/0.95  res_num_of_clauses:                     0
% 1.91/0.95  res_num_in_passive:                     0
% 1.91/0.95  res_num_in_active:                      0
% 1.91/0.95  res_num_of_loops:                       108
% 1.91/0.95  res_forward_subset_subsumed:            24
% 1.91/0.95  res_backward_subset_subsumed:           0
% 1.91/0.95  res_forward_subsumed:                   0
% 1.91/0.95  res_backward_subsumed:                  0
% 1.91/0.95  res_forward_subsumption_resolution:     0
% 1.91/0.95  res_backward_subsumption_resolution:    0
% 1.91/0.95  res_clause_to_clause_subsumption:       89
% 1.91/0.95  res_orphan_elimination:                 0
% 1.91/0.95  res_tautology_del:                      20
% 1.91/0.95  res_num_eq_res_simplified:              0
% 1.91/0.95  res_num_sel_changes:                    0
% 1.91/0.95  res_moves_from_active_to_pass:          0
% 1.91/0.95  
% 1.91/0.95  ------ Superposition
% 1.91/0.95  
% 1.91/0.95  sup_time_total:                         0.
% 1.91/0.95  sup_time_generating:                    0.
% 1.91/0.95  sup_time_sim_full:                      0.
% 1.91/0.95  sup_time_sim_immed:                     0.
% 1.91/0.95  
% 1.91/0.95  sup_num_of_clauses:                     39
% 1.91/0.95  sup_num_in_active:                      29
% 1.91/0.95  sup_num_in_passive:                     10
% 1.91/0.95  sup_num_of_loops:                       32
% 1.91/0.95  sup_fw_superposition:                   7
% 1.91/0.95  sup_bw_superposition:                   20
% 1.91/0.95  sup_immediate_simplified:               6
% 1.91/0.95  sup_given_eliminated:                   0
% 1.91/0.95  comparisons_done:                       0
% 1.91/0.95  comparisons_avoided:                    3
% 1.91/0.95  
% 1.91/0.95  ------ Simplifications
% 1.91/0.95  
% 1.91/0.95  
% 1.91/0.95  sim_fw_subset_subsumed:                 1
% 1.91/0.95  sim_bw_subset_subsumed:                 0
% 1.91/0.95  sim_fw_subsumed:                        5
% 1.91/0.95  sim_bw_subsumed:                        0
% 1.91/0.95  sim_fw_subsumption_res:                 1
% 1.91/0.95  sim_bw_subsumption_res:                 0
% 1.91/0.95  sim_tautology_del:                      0
% 1.91/0.95  sim_eq_tautology_del:                   2
% 1.91/0.95  sim_eq_res_simp:                        0
% 1.91/0.95  sim_fw_demodulated:                     0
% 1.91/0.95  sim_bw_demodulated:                     3
% 1.91/0.95  sim_light_normalised:                   0
% 1.91/0.95  sim_joinable_taut:                      0
% 1.91/0.95  sim_joinable_simp:                      0
% 1.91/0.95  sim_ac_normalised:                      0
% 1.91/0.95  sim_smt_subsumption:                    0
% 1.91/0.95  
%------------------------------------------------------------------------------
