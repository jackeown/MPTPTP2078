%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:29 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :  224 (3229 expanded)
%              Number of clauses        :  140 ( 855 expanded)
%              Number of leaves         :   26 ( 642 expanded)
%              Depth                    :   36
%              Number of atoms          :  850 (26353 expanded)
%              Number of equality atoms :  326 (1673 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK4)
          | ~ v1_subset_1(sK4,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK4)
          | v1_subset_1(sK4,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK4,X0)
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK3),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK3)) )
          & ( ~ r2_hidden(k3_yellow_0(sK3),X1)
            | v1_subset_1(X1,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v13_waybel_0(X1,sK3)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK3)
      & v1_yellow_0(sK3)
      & v5_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( r2_hidden(k3_yellow_0(sK3),sK4)
      | ~ v1_subset_1(sK4,u1_struct_0(sK3)) )
    & ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
      | v1_subset_1(sK4,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v13_waybel_0(sK4,sK3)
    & ~ v1_xboole_0(sK4)
    & l1_orders_2(sK3)
    & v1_yellow_0(sK3)
    & v5_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r1_orders_2(X0,X2,sK2(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK1(X0,X1),X3)
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK2(X0,X1),X1)
                & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1))
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1261,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1257,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2582,plain,
    ( X0 = X1
    | m1_subset_1(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1257])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1249,plain,
    ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5676,plain,
    ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),sK0(X1,u1_struct_0(X0)))) = sK0(X1,u1_struct_0(X0))
    | u1_struct_0(X0) = X1
    | r2_hidden(sK0(X1,u1_struct_0(X0)),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2582,c_1249])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1237,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2195,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1259])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1262,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2686,plain,
    ( u1_struct_0(sK3) = X0
    | r2_hidden(sK0(X0,u1_struct_0(sK3)),X0) != iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_1262])).

cnf(c_43201,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5676,c_2686])).

cnf(c_43412,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_43201,c_5676])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2202,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_1257])).

cnf(c_4131,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_1249])).

cnf(c_34,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_38,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4689,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4131,c_34,c_35,c_36,c_38])).

cnf(c_5670,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,X0))) = sK0(sK4,X0)
    | sK4 = X0
    | m1_subset_1(sK0(sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2582,c_4689])).

cnf(c_7978,plain,
    ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
    | k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
    | u1_struct_0(X0) = sK4
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5670,c_1249])).

cnf(c_8071,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
    | k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
    | u1_struct_0(X0) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7978])).

cnf(c_8073,plain,
    ( v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_8071])).

cnf(c_44173,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43412,c_33,c_32,c_31,c_29,c_8073])).

cnf(c_1234,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1255,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1862,plain,
    ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
    inference(superposition,[status(thm)],[c_1234,c_1255])).

cnf(c_11,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1252,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) = iProver_top
    | r1_yellow_0(X0,X2) != iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3114,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top
    | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1252])).

cnf(c_30,negated_conjecture,
    ( v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,plain,
    ( v1_yellow_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | ~ v1_yellow_0(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_66,plain,
    ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
    | v1_yellow_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_68,plain,
    ( r1_yellow_0(sK3,k1_xboole_0) = iProver_top
    | v1_yellow_0(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_101,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3143,plain,
    ( r1_yellow_0(sK3,X0) != iProver_top
    | r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3114,c_34,c_36,c_37,c_38,c_68,c_101])).

cnf(c_3144,plain,
    ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3143])).

cnf(c_44197,plain,
    ( u1_struct_0(sK3) = sK4
    | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(sK4,u1_struct_0(sK3))) = iProver_top
    | r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_44173,c_3144])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7373,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r2_hidden(sK0(sK4,X1),X0)
    | ~ r2_hidden(sK0(sK4,X1),sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_22522,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(sK4,X0),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_7373])).

cnf(c_35245,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_22522])).

cnf(c_35256,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35245])).

cnf(c_7368,plain,
    ( ~ r2_hidden(sK0(sK4,X0),X0)
    | ~ r2_hidden(sK0(sK4,X0),sK4)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_35254,plain,
    ( ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_7368])).

cnf(c_35262,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35254])).

cnf(c_9,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1254,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4127,plain,
    ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),k1_yellow_0(X0,X1))) = k1_yellow_0(X0,X1)
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1249])).

cnf(c_10768,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0)
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_4127])).

cnf(c_11007,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10768,c_34,c_35,c_36])).

cnf(c_21,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1242,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | v13_waybel_0(X3,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3242,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | v13_waybel_0(sK4,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1242])).

cnf(c_27,negated_conjecture,
    ( v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v13_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3452,plain,
    ( r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3242,c_38,c_40,c_2202])).

cnf(c_3453,plain,
    ( r1_orders_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3452])).

cnf(c_3462,plain,
    ( r1_yellow_0(sK3,X0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3144,c_3453])).

cnf(c_11068,plain,
    ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11007,c_3462])).

cnf(c_11070,plain,
    ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11068,c_11007])).

cnf(c_12,plain,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1251,plain,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3460,plain,
    ( r1_yellow_0(sK3,X0) != iProver_top
    | r1_yellow_0(sK3,X1) != iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X1),sK4) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_3453])).

cnf(c_3584,plain,
    ( r1_yellow_0(sK3,X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_3462])).

cnf(c_3115,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k3_yellow_0(sK3)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top
    | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1252])).

cnf(c_3800,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_orders_2(sK3,k1_yellow_0(sK3,X0),k3_yellow_0(sK3)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3115,c_34,c_36,c_37,c_38,c_68])).

cnf(c_3801,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k3_yellow_0(sK3)) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3800])).

cnf(c_3810,plain,
    ( r1_yellow_0(sK3,X0) != iProver_top
    | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_3453])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_43,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_81,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_83,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_388,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_407,plain,
    ( k3_yellow_0(sK3) = k3_yellow_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_380,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_421,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1583,plain,
    ( ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | r2_hidden(k3_yellow_0(X0),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1584,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) != iProver_top
    | r2_hidden(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_1586,plain,
    ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_22,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1793,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | X0 = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2364,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_2365,plain,
    ( sK4 = u1_struct_0(sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_387,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1758,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | X0 != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_3561,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(sK4)
    | sK4 != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_3562,plain,
    ( sK4 != u1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3561])).

cnf(c_3564,plain,
    ( sK4 != u1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3562])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2290,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_2776,plain,
    ( ~ r2_hidden(k3_yellow_0(X0),X1)
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(X0)
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_2290])).

cnf(c_3747,plain,
    ( ~ r2_hidden(k3_yellow_0(X0),u1_struct_0(X0))
    | r2_hidden(k3_yellow_0(sK3),sK4)
    | k3_yellow_0(sK3) != k3_yellow_0(X0)
    | sK4 != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_3748,plain,
    ( k3_yellow_0(sK3) != k3_yellow_0(X0)
    | sK4 != u1_struct_0(X0)
    | r2_hidden(k3_yellow_0(X0),u1_struct_0(X0)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3747])).

cnf(c_3750,plain,
    ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
    | sK4 != u1_struct_0(sK3)
    | r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3748])).

cnf(c_3825,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3810,c_38,c_39,c_41,c_43,c_83,c_407,c_421,c_1586,c_2365,c_3564,c_3750])).

cnf(c_4018,plain,
    ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | r1_yellow_0(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_38,c_39,c_41,c_43,c_83,c_407,c_421,c_1586,c_2365,c_3564,c_3584,c_3750])).

cnf(c_4019,plain,
    ( r1_yellow_0(sK3,X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_4018])).

cnf(c_4701,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0)
    | r1_yellow_0(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4019,c_4689])).

cnf(c_4879,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_4701])).

cnf(c_9359,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4879,c_34,c_35,c_36,c_38])).

cnf(c_9373,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0))
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_9359])).

cnf(c_9864,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0)))
    | r1_yellow_0(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4019,c_9373])).

cnf(c_9367,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0)))
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_9359])).

cnf(c_9936,plain,
    ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9864,c_38,c_9367])).

cnf(c_9946,plain,
    ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_9936,c_4019])).

cnf(c_11015,plain,
    ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11007,c_9946])).

cnf(c_11642,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_11015])).

cnf(c_12100,plain,
    ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11070,c_34,c_35,c_36,c_38,c_11642])).

cnf(c_12101,plain,
    ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_12100])).

cnf(c_12108,plain,
    ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_12101])).

cnf(c_13342,plain,
    ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12108,c_38])).

cnf(c_44186,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_44173,c_13342])).

cnf(c_44698,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_44197,c_41,c_35256,c_35262,c_44186])).

cnf(c_25,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1238,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3831,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3825,c_1238])).

cnf(c_44830,plain,
    ( v1_subset_1(sK4,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_44698,c_3831])).

cnf(c_5,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1258,plain,
    ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1283,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1258,c_3])).

cnf(c_46748,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44830,c_1283])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:47:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 11.66/1.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.66/1.97  
% 11.66/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.66/1.97  
% 11.66/1.97  ------  iProver source info
% 11.66/1.97  
% 11.66/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.66/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.66/1.97  git: non_committed_changes: false
% 11.66/1.97  git: last_make_outside_of_git: false
% 11.66/1.97  
% 11.66/1.97  ------ 
% 11.66/1.97  ------ Parsing...
% 11.66/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.66/1.97  
% 11.66/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.66/1.97  
% 11.66/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.66/1.97  
% 11.66/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.66/1.97  ------ Proving...
% 11.66/1.97  ------ Problem Properties 
% 11.66/1.97  
% 11.66/1.97  
% 11.66/1.97  clauses                                 34
% 11.66/1.97  conjectures                             10
% 11.66/1.97  EPR                                     11
% 11.66/1.97  Horn                                    23
% 11.66/1.97  unary                                   11
% 11.66/1.97  binary                                  7
% 11.66/1.97  lits                                    96
% 11.66/1.97  lits eq                                 7
% 11.66/1.97  fd_pure                                 0
% 11.66/1.97  fd_pseudo                               0
% 11.66/1.97  fd_cond                                 0
% 11.66/1.97  fd_pseudo_cond                          3
% 11.66/1.97  AC symbols                              0
% 11.66/1.97  
% 11.66/1.97  ------ Input Options Time Limit: Unbounded
% 11.66/1.97  
% 11.66/1.97  
% 11.66/1.97  ------ 
% 11.66/1.97  Current options:
% 11.66/1.97  ------ 
% 11.66/1.97  
% 11.66/1.97  
% 11.66/1.97  
% 11.66/1.97  
% 11.66/1.97  ------ Proving...
% 11.66/1.97  
% 11.66/1.97  
% 11.66/1.97  % SZS status Theorem for theBenchmark.p
% 11.66/1.97  
% 11.66/1.97   Resolution empty clause
% 11.66/1.97  
% 11.66/1.97  % SZS output start CNFRefutation for theBenchmark.p
% 11.66/1.97  
% 11.66/1.97  fof(f1,axiom,(
% 11.66/1.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f23,plain,(
% 11.66/1.97    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 11.66/1.97    inference(ennf_transformation,[],[f1])).
% 11.66/1.97  
% 11.66/1.97  fof(f44,plain,(
% 11.66/1.97    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 11.66/1.97    inference(nnf_transformation,[],[f23])).
% 11.66/1.97  
% 11.66/1.97  fof(f45,plain,(
% 11.66/1.97    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 11.66/1.97    introduced(choice_axiom,[])).
% 11.66/1.97  
% 11.66/1.97  fof(f46,plain,(
% 11.66/1.97    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 11.66/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 11.66/1.97  
% 11.66/1.97  fof(f58,plain,(
% 11.66/1.97    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f46])).
% 11.66/1.97  
% 11.66/1.97  fof(f6,axiom,(
% 11.66/1.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f25,plain,(
% 11.66/1.97    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 11.66/1.97    inference(ennf_transformation,[],[f6])).
% 11.66/1.97  
% 11.66/1.97  fof(f64,plain,(
% 11.66/1.97    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f25])).
% 11.66/1.97  
% 11.66/1.97  fof(f13,axiom,(
% 11.66/1.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f35,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : ((k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.66/1.97    inference(ennf_transformation,[],[f13])).
% 11.66/1.97  
% 11.66/1.97  fof(f36,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : ((k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.66/1.97    inference(flattening,[],[f35])).
% 11.66/1.97  
% 11.66/1.97  fof(f71,plain,(
% 11.66/1.97    ( ! [X0,X1] : (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f36])).
% 11.66/1.97  
% 11.66/1.97  fof(f17,conjecture,(
% 11.66/1.97    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f18,negated_conjecture,(
% 11.66/1.97    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 11.66/1.97    inference(negated_conjecture,[],[f17])).
% 11.66/1.97  
% 11.66/1.97  fof(f19,plain,(
% 11.66/1.97    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 11.66/1.97    inference(pure_predicate_removal,[],[f18])).
% 11.66/1.97  
% 11.66/1.97  fof(f20,plain,(
% 11.66/1.97    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 11.66/1.97    inference(pure_predicate_removal,[],[f19])).
% 11.66/1.97  
% 11.66/1.97  fof(f42,plain,(
% 11.66/1.97    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.66/1.97    inference(ennf_transformation,[],[f20])).
% 11.66/1.97  
% 11.66/1.97  fof(f43,plain,(
% 11.66/1.97    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.66/1.97    inference(flattening,[],[f42])).
% 11.66/1.97  
% 11.66/1.97  fof(f53,plain,(
% 11.66/1.97    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.66/1.97    inference(nnf_transformation,[],[f43])).
% 11.66/1.97  
% 11.66/1.97  fof(f54,plain,(
% 11.66/1.97    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.66/1.97    inference(flattening,[],[f53])).
% 11.66/1.97  
% 11.66/1.97  fof(f56,plain,(
% 11.66/1.97    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK4) | ~v1_subset_1(sK4,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK4) | v1_subset_1(sK4,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK4,X0) & ~v1_xboole_0(sK4))) )),
% 11.66/1.97    introduced(choice_axiom,[])).
% 11.66/1.97  
% 11.66/1.97  fof(f55,plain,(
% 11.66/1.97    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 11.66/1.97    introduced(choice_axiom,[])).
% 11.66/1.97  
% 11.66/1.97  fof(f57,plain,(
% 11.66/1.97    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 11.66/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).
% 11.66/1.97  
% 11.66/1.97  fof(f89,plain,(
% 11.66/1.97    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f4,axiom,(
% 11.66/1.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f24,plain,(
% 11.66/1.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.66/1.97    inference(ennf_transformation,[],[f4])).
% 11.66/1.97  
% 11.66/1.97  fof(f62,plain,(
% 11.66/1.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.66/1.97    inference(cnf_transformation,[],[f24])).
% 11.66/1.97  
% 11.66/1.97  fof(f59,plain,(
% 11.66/1.97    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f46])).
% 11.66/1.97  
% 11.66/1.97  fof(f82,plain,(
% 11.66/1.97    ~v2_struct_0(sK3)),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f83,plain,(
% 11.66/1.97    v3_orders_2(sK3)),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f84,plain,(
% 11.66/1.97    v5_orders_2(sK3)),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f86,plain,(
% 11.66/1.97    l1_orders_2(sK3)),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f8,axiom,(
% 11.66/1.97    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f28,plain,(
% 11.66/1.97    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(ennf_transformation,[],[f8])).
% 11.66/1.97  
% 11.66/1.97  fof(f66,plain,(
% 11.66/1.97    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f28])).
% 11.66/1.97  
% 11.66/1.97  fof(f11,axiom,(
% 11.66/1.97    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f31,plain,(
% 11.66/1.97    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(ennf_transformation,[],[f11])).
% 11.66/1.97  
% 11.66/1.97  fof(f32,plain,(
% 11.66/1.97    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(flattening,[],[f31])).
% 11.66/1.97  
% 11.66/1.97  fof(f69,plain,(
% 11.66/1.97    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f32])).
% 11.66/1.97  
% 11.66/1.97  fof(f85,plain,(
% 11.66/1.97    v1_yellow_0(sK3)),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f14,axiom,(
% 11.66/1.97    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f21,plain,(
% 11.66/1.97    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 11.66/1.97    inference(pure_predicate_removal,[],[f14])).
% 11.66/1.97  
% 11.66/1.97  fof(f37,plain,(
% 11.66/1.97    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 11.66/1.97    inference(ennf_transformation,[],[f21])).
% 11.66/1.97  
% 11.66/1.97  fof(f38,plain,(
% 11.66/1.97    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.66/1.97    inference(flattening,[],[f37])).
% 11.66/1.97  
% 11.66/1.97  fof(f73,plain,(
% 11.66/1.97    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f38])).
% 11.66/1.97  
% 11.66/1.97  fof(f2,axiom,(
% 11.66/1.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f60,plain,(
% 11.66/1.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f2])).
% 11.66/1.97  
% 11.66/1.97  fof(f9,axiom,(
% 11.66/1.97    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f29,plain,(
% 11.66/1.97    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(ennf_transformation,[],[f9])).
% 11.66/1.97  
% 11.66/1.97  fof(f67,plain,(
% 11.66/1.97    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f29])).
% 11.66/1.97  
% 11.66/1.97  fof(f15,axiom,(
% 11.66/1.97    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f39,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(ennf_transformation,[],[f15])).
% 11.66/1.97  
% 11.66/1.97  fof(f40,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(flattening,[],[f39])).
% 11.66/1.97  
% 11.66/1.97  fof(f47,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(nnf_transformation,[],[f40])).
% 11.66/1.97  
% 11.66/1.97  fof(f48,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(rectify,[],[f47])).
% 11.66/1.97  
% 11.66/1.97  fof(f50,plain,(
% 11.66/1.97    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,X2,sK2(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))) )),
% 11.66/1.97    introduced(choice_axiom,[])).
% 11.66/1.97  
% 11.66/1.97  fof(f49,plain,(
% 11.66/1.97    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK1(X0,X1),X3) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 11.66/1.97    introduced(choice_axiom,[])).
% 11.66/1.97  
% 11.66/1.97  fof(f51,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK2(X0,X1),X1) & r1_orders_2(X0,sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 11.66/1.97  
% 11.66/1.97  fof(f74,plain,(
% 11.66/1.97    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f51])).
% 11.66/1.97  
% 11.66/1.97  fof(f88,plain,(
% 11.66/1.97    v13_waybel_0(sK4,sK3)),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f12,axiom,(
% 11.66/1.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f22,plain,(
% 11.66/1.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))))),
% 11.66/1.97    inference(pure_predicate_removal,[],[f12])).
% 11.66/1.97  
% 11.66/1.97  fof(f33,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : (r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.66/1.97    inference(ennf_transformation,[],[f22])).
% 11.66/1.97  
% 11.66/1.97  fof(f34,plain,(
% 11.66/1.97    ! [X0] : (! [X1] : (r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.66/1.97    inference(flattening,[],[f33])).
% 11.66/1.97  
% 11.66/1.97  fof(f70,plain,(
% 11.66/1.97    ( ! [X0,X1] : (r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f34])).
% 11.66/1.97  
% 11.66/1.97  fof(f87,plain,(
% 11.66/1.97    ~v1_xboole_0(sK4)),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f91,plain,(
% 11.66/1.97    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f10,axiom,(
% 11.66/1.97    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f30,plain,(
% 11.66/1.97    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 11.66/1.97    inference(ennf_transformation,[],[f10])).
% 11.66/1.97  
% 11.66/1.97  fof(f68,plain,(
% 11.66/1.97    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f30])).
% 11.66/1.97  
% 11.66/1.97  fof(f7,axiom,(
% 11.66/1.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f26,plain,(
% 11.66/1.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.66/1.97    inference(ennf_transformation,[],[f7])).
% 11.66/1.97  
% 11.66/1.97  fof(f27,plain,(
% 11.66/1.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.66/1.97    inference(flattening,[],[f26])).
% 11.66/1.97  
% 11.66/1.97  fof(f65,plain,(
% 11.66/1.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f27])).
% 11.66/1.97  
% 11.66/1.97  fof(f16,axiom,(
% 11.66/1.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f41,plain,(
% 11.66/1.97    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.66/1.97    inference(ennf_transformation,[],[f16])).
% 11.66/1.97  
% 11.66/1.97  fof(f52,plain,(
% 11.66/1.97    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.66/1.97    inference(nnf_transformation,[],[f41])).
% 11.66/1.97  
% 11.66/1.97  fof(f81,plain,(
% 11.66/1.97    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.66/1.97    inference(cnf_transformation,[],[f52])).
% 11.66/1.97  
% 11.66/1.97  fof(f90,plain,(
% 11.66/1.97    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 11.66/1.97    inference(cnf_transformation,[],[f57])).
% 11.66/1.97  
% 11.66/1.97  fof(f5,axiom,(
% 11.66/1.97    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f63,plain,(
% 11.66/1.97    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 11.66/1.97    inference(cnf_transformation,[],[f5])).
% 11.66/1.97  
% 11.66/1.97  fof(f3,axiom,(
% 11.66/1.97    ! [X0] : k2_subset_1(X0) = X0),
% 11.66/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/1.97  
% 11.66/1.97  fof(f61,plain,(
% 11.66/1.97    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.66/1.97    inference(cnf_transformation,[],[f3])).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1,plain,
% 11.66/1.97      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 11.66/1.97      inference(cnf_transformation,[],[f58]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1261,plain,
% 11.66/1.97      ( X0 = X1
% 11.66/1.97      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 11.66/1.97      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_6,plain,
% 11.66/1.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 11.66/1.97      inference(cnf_transformation,[],[f64]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1257,plain,
% 11.66/1.97      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2582,plain,
% 11.66/1.97      ( X0 = X1
% 11.66/1.97      | m1_subset_1(sK0(X0,X1),X1) = iProver_top
% 11.66/1.97      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1261,c_1257]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_14,plain,
% 11.66/1.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.66/1.97      | v2_struct_0(X1)
% 11.66/1.97      | ~ v3_orders_2(X1)
% 11.66/1.97      | ~ v5_orders_2(X1)
% 11.66/1.97      | ~ l1_orders_2(X1)
% 11.66/1.97      | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
% 11.66/1.97      inference(cnf_transformation,[],[f71]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1249,plain,
% 11.66/1.97      ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
% 11.66/1.97      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.66/1.97      | v2_struct_0(X0) = iProver_top
% 11.66/1.97      | v3_orders_2(X0) != iProver_top
% 11.66/1.97      | v5_orders_2(X0) != iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_5676,plain,
% 11.66/1.97      ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),sK0(X1,u1_struct_0(X0)))) = sK0(X1,u1_struct_0(X0))
% 11.66/1.97      | u1_struct_0(X0) = X1
% 11.66/1.97      | r2_hidden(sK0(X1,u1_struct_0(X0)),X1) = iProver_top
% 11.66/1.97      | v2_struct_0(X0) = iProver_top
% 11.66/1.97      | v3_orders_2(X0) != iProver_top
% 11.66/1.97      | v5_orders_2(X0) != iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_2582,c_1249]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_26,negated_conjecture,
% 11.66/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 11.66/1.97      inference(cnf_transformation,[],[f89]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1237,plain,
% 11.66/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4,plain,
% 11.66/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.66/1.97      | ~ r2_hidden(X2,X0)
% 11.66/1.97      | r2_hidden(X2,X1) ),
% 11.66/1.97      inference(cnf_transformation,[],[f62]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1259,plain,
% 11.66/1.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.66/1.97      | r2_hidden(X2,X0) != iProver_top
% 11.66/1.97      | r2_hidden(X2,X1) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2195,plain,
% 11.66/1.97      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1237,c_1259]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_0,plain,
% 11.66/1.97      ( ~ r2_hidden(sK0(X0,X1),X1) | ~ r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 11.66/1.97      inference(cnf_transformation,[],[f59]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1262,plain,
% 11.66/1.97      ( X0 = X1
% 11.66/1.97      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 11.66/1.97      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2686,plain,
% 11.66/1.97      ( u1_struct_0(sK3) = X0
% 11.66/1.97      | r2_hidden(sK0(X0,u1_struct_0(sK3)),X0) != iProver_top
% 11.66/1.97      | r2_hidden(sK0(X0,u1_struct_0(sK3)),sK4) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_2195,c_1262]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_43201,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
% 11.66/1.97      | u1_struct_0(sK3) = sK4
% 11.66/1.97      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top
% 11.66/1.97      | v2_struct_0(sK3) = iProver_top
% 11.66/1.97      | v3_orders_2(sK3) != iProver_top
% 11.66/1.97      | v5_orders_2(sK3) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_5676,c_2686]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_43412,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
% 11.66/1.97      | u1_struct_0(sK3) = sK4
% 11.66/1.97      | v2_struct_0(sK3) = iProver_top
% 11.66/1.97      | v3_orders_2(sK3) != iProver_top
% 11.66/1.97      | v5_orders_2(sK3) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_43201,c_5676]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_33,negated_conjecture,
% 11.66/1.97      ( ~ v2_struct_0(sK3) ),
% 11.66/1.97      inference(cnf_transformation,[],[f82]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_32,negated_conjecture,
% 11.66/1.97      ( v3_orders_2(sK3) ),
% 11.66/1.97      inference(cnf_transformation,[],[f83]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_31,negated_conjecture,
% 11.66/1.97      ( v5_orders_2(sK3) ),
% 11.66/1.97      inference(cnf_transformation,[],[f84]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_29,negated_conjecture,
% 11.66/1.97      ( l1_orders_2(sK3) ),
% 11.66/1.97      inference(cnf_transformation,[],[f86]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2202,plain,
% 11.66/1.97      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_2195,c_1257]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4131,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = X0
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top
% 11.66/1.97      | v2_struct_0(sK3) = iProver_top
% 11.66/1.97      | v3_orders_2(sK3) != iProver_top
% 11.66/1.97      | v5_orders_2(sK3) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_2202,c_1249]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_34,plain,
% 11.66/1.97      ( v2_struct_0(sK3) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_35,plain,
% 11.66/1.97      ( v3_orders_2(sK3) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_36,plain,
% 11.66/1.97      ( v5_orders_2(sK3) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_38,plain,
% 11.66/1.97      ( l1_orders_2(sK3) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4689,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = X0
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_4131,c_34,c_35,c_36,c_38]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_5670,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,X0))) = sK0(sK4,X0)
% 11.66/1.97      | sK4 = X0
% 11.66/1.97      | m1_subset_1(sK0(sK4,X0),X0) = iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_2582,c_4689]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_7978,plain,
% 11.66/1.97      ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
% 11.66/1.97      | k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
% 11.66/1.97      | u1_struct_0(X0) = sK4
% 11.66/1.97      | v2_struct_0(X0) = iProver_top
% 11.66/1.97      | v3_orders_2(X0) != iProver_top
% 11.66/1.97      | v5_orders_2(X0) != iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_5670,c_1249]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_8071,plain,
% 11.66/1.97      ( v2_struct_0(X0)
% 11.66/1.97      | ~ v3_orders_2(X0)
% 11.66/1.97      | ~ v5_orders_2(X0)
% 11.66/1.97      | ~ l1_orders_2(X0)
% 11.66/1.97      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
% 11.66/1.97      | k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(X0)))) = sK0(sK4,u1_struct_0(X0))
% 11.66/1.97      | u1_struct_0(X0) = sK4 ),
% 11.66/1.97      inference(predicate_to_equality_rev,[status(thm)],[c_7978]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_8073,plain,
% 11.66/1.97      ( v2_struct_0(sK3)
% 11.66/1.97      | ~ v3_orders_2(sK3)
% 11.66/1.97      | ~ v5_orders_2(sK3)
% 11.66/1.97      | ~ l1_orders_2(sK3)
% 11.66/1.97      | k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
% 11.66/1.97      | u1_struct_0(sK3) = sK4 ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_8071]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_44173,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) = sK0(sK4,u1_struct_0(sK3))
% 11.66/1.97      | u1_struct_0(sK3) = sK4 ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_43412,c_33,c_32,c_31,c_29,c_8073]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1234,plain,
% 11.66/1.97      ( l1_orders_2(sK3) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_8,plain,
% 11.66/1.97      ( ~ l1_orders_2(X0) | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f66]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1255,plain,
% 11.66/1.97      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1862,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k1_xboole_0) = k3_yellow_0(sK3) ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1234,c_1255]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_11,plain,
% 11.66/1.97      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 11.66/1.97      | ~ r1_yellow_0(X0,X2)
% 11.66/1.97      | ~ r1_yellow_0(X0,X1)
% 11.66/1.97      | ~ r1_tarski(X1,X2)
% 11.66/1.97      | ~ l1_orders_2(X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f69]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1252,plain,
% 11.66/1.97      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) = iProver_top
% 11.66/1.97      | r1_yellow_0(X0,X2) != iProver_top
% 11.66/1.97      | r1_yellow_0(X0,X1) != iProver_top
% 11.66/1.97      | r1_tarski(X1,X2) != iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3114,plain,
% 11.66/1.97      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
% 11.66/1.97      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1862,c_1252]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_30,negated_conjecture,
% 11.66/1.97      ( v1_yellow_0(sK3) ),
% 11.66/1.97      inference(cnf_transformation,[],[f85]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_37,plain,
% 11.66/1.97      ( v1_yellow_0(sK3) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_15,plain,
% 11.66/1.97      ( r1_yellow_0(X0,k1_xboole_0)
% 11.66/1.97      | ~ v1_yellow_0(X0)
% 11.66/1.97      | v2_struct_0(X0)
% 11.66/1.97      | ~ v5_orders_2(X0)
% 11.66/1.97      | ~ l1_orders_2(X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f73]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_66,plain,
% 11.66/1.97      ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
% 11.66/1.97      | v1_yellow_0(X0) != iProver_top
% 11.66/1.97      | v2_struct_0(X0) = iProver_top
% 11.66/1.97      | v5_orders_2(X0) != iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_68,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,k1_xboole_0) = iProver_top
% 11.66/1.97      | v1_yellow_0(sK3) != iProver_top
% 11.66/1.97      | v2_struct_0(sK3) = iProver_top
% 11.66/1.97      | v5_orders_2(sK3) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_66]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2,plain,
% 11.66/1.97      ( r1_tarski(k1_xboole_0,X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f60]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_101,plain,
% 11.66/1.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3143,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_3114,c_34,c_36,c_37,c_38,c_68,c_101]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3144,plain,
% 11.66/1.97      ( r1_orders_2(sK3,k3_yellow_0(sK3),k1_yellow_0(sK3,X0)) = iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top ),
% 11.66/1.97      inference(renaming,[status(thm)],[c_3143]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_44197,plain,
% 11.66/1.97      ( u1_struct_0(sK3) = sK4
% 11.66/1.97      | r1_orders_2(sK3,k3_yellow_0(sK3),sK0(sK4,u1_struct_0(sK3))) = iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),sK0(sK4,u1_struct_0(sK3)))) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_44173,c_3144]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_41,plain,
% 11.66/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_7373,plain,
% 11.66/1.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 11.66/1.97      | r2_hidden(sK0(sK4,X1),X0)
% 11.66/1.97      | ~ r2_hidden(sK0(sK4,X1),sK4) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_4]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_22522,plain,
% 11.66/1.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.66/1.97      | r2_hidden(sK0(sK4,X0),u1_struct_0(sK3))
% 11.66/1.97      | ~ r2_hidden(sK0(sK4,X0),sK4) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_7373]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_35245,plain,
% 11.66/1.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.66/1.97      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 11.66/1.97      | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_22522]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_35256,plain,
% 11.66/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.66/1.97      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 11.66/1.97      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_35245]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_7368,plain,
% 11.66/1.97      ( ~ r2_hidden(sK0(sK4,X0),X0) | ~ r2_hidden(sK0(sK4,X0),sK4) | X0 = sK4 ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_0]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_35254,plain,
% 11.66/1.97      ( ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
% 11.66/1.97      | ~ r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4)
% 11.66/1.97      | u1_struct_0(sK3) = sK4 ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_7368]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_35262,plain,
% 11.66/1.97      ( u1_struct_0(sK3) = sK4
% 11.66/1.97      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_35254]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_9,plain,
% 11.66/1.97      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~ l1_orders_2(X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f67]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1254,plain,
% 11.66/1.97      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4127,plain,
% 11.66/1.97      ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),k1_yellow_0(X0,X1))) = k1_yellow_0(X0,X1)
% 11.66/1.97      | v2_struct_0(X0) = iProver_top
% 11.66/1.97      | v3_orders_2(X0) != iProver_top
% 11.66/1.97      | v5_orders_2(X0) != iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1254,c_1249]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_10768,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0)
% 11.66/1.97      | v2_struct_0(sK3) = iProver_top
% 11.66/1.97      | v3_orders_2(sK3) != iProver_top
% 11.66/1.97      | v5_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1234,c_4127]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_11007,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0) ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_10768,c_34,c_35,c_36]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_21,plain,
% 11.66/1.97      ( ~ r1_orders_2(X0,X1,X2)
% 11.66/1.97      | ~ v13_waybel_0(X3,X0)
% 11.66/1.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.66/1.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/1.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 11.66/1.97      | ~ r2_hidden(X1,X3)
% 11.66/1.97      | r2_hidden(X2,X3)
% 11.66/1.97      | ~ l1_orders_2(X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f74]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1242,plain,
% 11.66/1.97      ( r1_orders_2(X0,X1,X2) != iProver_top
% 11.66/1.97      | v13_waybel_0(X3,X0) != iProver_top
% 11.66/1.97      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.66/1.97      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.66/1.97      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.66/1.97      | r2_hidden(X1,X3) != iProver_top
% 11.66/1.97      | r2_hidden(X2,X3) = iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3242,plain,
% 11.66/1.97      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 11.66/1.97      | v13_waybel_0(sK4,sK3) != iProver_top
% 11.66/1.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top
% 11.66/1.97      | r2_hidden(X1,sK4) = iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1237,c_1242]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_27,negated_conjecture,
% 11.66/1.97      ( v13_waybel_0(sK4,sK3) ),
% 11.66/1.97      inference(cnf_transformation,[],[f88]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_40,plain,
% 11.66/1.97      ( v13_waybel_0(sK4,sK3) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3452,plain,
% 11.66/1.97      ( r2_hidden(X1,sK4) = iProver_top
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top
% 11.66/1.97      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r1_orders_2(sK3,X0,X1) != iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_3242,c_38,c_40,c_2202]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3453,plain,
% 11.66/1.97      ( r1_orders_2(sK3,X0,X1) != iProver_top
% 11.66/1.97      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top
% 11.66/1.97      | r2_hidden(X1,sK4) = iProver_top ),
% 11.66/1.97      inference(renaming,[status(thm)],[c_3452]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3462,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_3144,c_3453]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_11068,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) != iProver_top
% 11.66/1.97      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))),sK4) = iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_11007,c_3462]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_11070,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) != iProver_top
% 11.66/1.97      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 11.66/1.97      inference(light_normalisation,[status(thm)],[c_11068,c_11007]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_12,plain,
% 11.66/1.97      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
% 11.66/1.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.66/1.97      | v2_struct_0(X0)
% 11.66/1.97      | ~ v3_orders_2(X0)
% 11.66/1.97      | ~ v5_orders_2(X0)
% 11.66/1.97      | ~ l1_orders_2(X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f70]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1251,plain,
% 11.66/1.97      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = iProver_top
% 11.66/1.97      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.66/1.97      | v2_struct_0(X0) = iProver_top
% 11.66/1.97      | v3_orders_2(X0) != iProver_top
% 11.66/1.97      | v5_orders_2(X0) != iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3460,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,X1) != iProver_top
% 11.66/1.97      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r1_tarski(X1,X0) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X1),sK4) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1252,c_3453]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3584,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1254,c_3462]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3115,plain,
% 11.66/1.97      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k3_yellow_0(sK3)) = iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,k1_xboole_0) != iProver_top
% 11.66/1.97      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1862,c_1252]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3800,plain,
% 11.66/1.97      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 11.66/1.97      | r1_orders_2(sK3,k1_yellow_0(sK3,X0),k3_yellow_0(sK3)) = iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_3115,c_34,c_36,c_37,c_38,c_68]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3801,plain,
% 11.66/1.97      ( r1_orders_2(sK3,k1_yellow_0(sK3,X0),k3_yellow_0(sK3)) = iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.66/1.97      inference(renaming,[status(thm)],[c_3800]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3810,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) != iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_3801,c_3453]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_28,negated_conjecture,
% 11.66/1.97      ( ~ v1_xboole_0(sK4) ),
% 11.66/1.97      inference(cnf_transformation,[],[f87]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_39,plain,
% 11.66/1.97      ( v1_xboole_0(sK4) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_24,negated_conjecture,
% 11.66/1.97      ( ~ v1_subset_1(sK4,u1_struct_0(sK3)) | r2_hidden(k3_yellow_0(sK3),sK4) ),
% 11.66/1.97      inference(cnf_transformation,[],[f91]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_43,plain,
% 11.66/1.97      ( v1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_10,plain,
% 11.66/1.97      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~ l1_orders_2(X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f68]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_81,plain,
% 11.66/1.97      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 11.66/1.97      | l1_orders_2(X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_83,plain,
% 11.66/1.97      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_81]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_388,plain,
% 11.66/1.97      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 11.66/1.97      theory(equality) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_407,plain,
% 11.66/1.97      ( k3_yellow_0(sK3) = k3_yellow_0(sK3) | sK3 != sK3 ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_388]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_380,plain,( X0 = X0 ),theory(equality) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_421,plain,
% 11.66/1.97      ( sK3 = sK3 ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_380]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_7,plain,
% 11.66/1.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.66/1.97      inference(cnf_transformation,[],[f65]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1583,plain,
% 11.66/1.97      ( ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 11.66/1.97      | r2_hidden(k3_yellow_0(X0),u1_struct_0(X0))
% 11.66/1.97      | v1_xboole_0(u1_struct_0(X0)) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_7]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1584,plain,
% 11.66/1.97      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) != iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 11.66/1.97      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1586,plain,
% 11.66/1.97      ( m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
% 11.66/1.97      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_1584]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_22,plain,
% 11.66/1.97      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 11.66/1.97      inference(cnf_transformation,[],[f81]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1793,plain,
% 11.66/1.97      ( v1_subset_1(X0,u1_struct_0(X1))
% 11.66/1.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.66/1.97      | X0 = u1_struct_0(X1) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_22]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2364,plain,
% 11.66/1.97      ( v1_subset_1(sK4,u1_struct_0(sK3))
% 11.66/1.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.66/1.97      | sK4 = u1_struct_0(sK3) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_1793]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2365,plain,
% 11.66/1.97      ( sK4 = u1_struct_0(sK3)
% 11.66/1.97      | v1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
% 11.66/1.97      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_2364]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_387,plain,
% 11.66/1.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.66/1.97      theory(equality) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1758,plain,
% 11.66/1.97      ( v1_xboole_0(X0)
% 11.66/1.97      | ~ v1_xboole_0(u1_struct_0(X1))
% 11.66/1.97      | X0 != u1_struct_0(X1) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_387]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3561,plain,
% 11.66/1.97      ( ~ v1_xboole_0(u1_struct_0(X0))
% 11.66/1.97      | v1_xboole_0(sK4)
% 11.66/1.97      | sK4 != u1_struct_0(X0) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_1758]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3562,plain,
% 11.66/1.97      ( sK4 != u1_struct_0(X0)
% 11.66/1.97      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 11.66/1.97      | v1_xboole_0(sK4) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_3561]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3564,plain,
% 11.66/1.97      ( sK4 != u1_struct_0(sK3)
% 11.66/1.97      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | v1_xboole_0(sK4) = iProver_top ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_3562]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_382,plain,
% 11.66/1.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.66/1.97      theory(equality) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2290,plain,
% 11.66/1.97      ( ~ r2_hidden(X0,X1)
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4)
% 11.66/1.97      | k3_yellow_0(sK3) != X0
% 11.66/1.97      | sK4 != X1 ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_382]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_2776,plain,
% 11.66/1.97      ( ~ r2_hidden(k3_yellow_0(X0),X1)
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4)
% 11.66/1.97      | k3_yellow_0(sK3) != k3_yellow_0(X0)
% 11.66/1.97      | sK4 != X1 ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_2290]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3747,plain,
% 11.66/1.97      ( ~ r2_hidden(k3_yellow_0(X0),u1_struct_0(X0))
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4)
% 11.66/1.97      | k3_yellow_0(sK3) != k3_yellow_0(X0)
% 11.66/1.97      | sK4 != u1_struct_0(X0) ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_2776]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3748,plain,
% 11.66/1.97      ( k3_yellow_0(sK3) != k3_yellow_0(X0)
% 11.66/1.97      | sK4 != u1_struct_0(X0)
% 11.66/1.97      | r2_hidden(k3_yellow_0(X0),u1_struct_0(X0)) != iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_3747]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3750,plain,
% 11.66/1.97      ( k3_yellow_0(sK3) != k3_yellow_0(sK3)
% 11.66/1.97      | sK4 != u1_struct_0(sK3)
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 11.66/1.97      inference(instantiation,[status(thm)],[c_3748]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3825,plain,
% 11.66/1.97      ( r2_hidden(k3_yellow_0(sK3),sK4) = iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_3810,c_38,c_39,c_41,c_43,c_83,c_407,c_421,c_1586,c_2365,
% 11.66/1.97                 c_3564,c_3750]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4018,plain,
% 11.66/1.97      ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_3460,c_38,c_39,c_41,c_43,c_83,c_407,c_421,c_1586,c_2365,
% 11.66/1.97                 c_3564,c_3584,c_3750]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4019,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,X0) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 11.66/1.97      inference(renaming,[status(thm)],[c_4018]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4701,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) = k1_yellow_0(sK3,X0)
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_4019,c_4689]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_4879,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0))
% 11.66/1.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | v2_struct_0(sK3) = iProver_top
% 11.66/1.97      | v3_orders_2(sK3) != iProver_top
% 11.66/1.97      | v5_orders_2(sK3) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1251,c_4701]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_9359,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0))
% 11.66/1.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_4879,c_34,c_35,c_36,c_38]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_9373,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0)))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),X0))
% 11.66/1.97      | r2_hidden(X0,sK4) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_2202,c_9359]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_9864,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0)))
% 11.66/1.97      | r1_yellow_0(sK3,X0) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_4019,c_9373]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_9367,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0)))
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1254,c_9359]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_9936,plain,
% 11.66/1.97      ( k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) = k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_9864,c_38,c_9367]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_9946,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))))) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))),sK4) = iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_9936,c_4019]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_11015,plain,
% 11.66/1.97      ( r1_yellow_0(sK3,k6_domain_1(u1_struct_0(sK3),k1_yellow_0(sK3,X0))) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 11.66/1.97      inference(demodulation,[status(thm)],[c_11007,c_9946]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_11642,plain,
% 11.66/1.97      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | v2_struct_0(sK3) = iProver_top
% 11.66/1.97      | v3_orders_2(sK3) != iProver_top
% 11.66/1.97      | v5_orders_2(sK3) != iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1251,c_11015]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_12100,plain,
% 11.66/1.97      ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_11070,c_34,c_35,c_36,c_38,c_11642]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_12101,plain,
% 11.66/1.97      ( m1_subset_1(k1_yellow_0(sK3,X0),u1_struct_0(sK3)) != iProver_top
% 11.66/1.97      | r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 11.66/1.97      inference(renaming,[status(thm)],[c_12100]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_12108,plain,
% 11.66/1.97      ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top
% 11.66/1.97      | l1_orders_2(sK3) != iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_1254,c_12101]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_13342,plain,
% 11.66/1.97      ( r2_hidden(k1_yellow_0(sK3,X0),sK4) = iProver_top ),
% 11.66/1.97      inference(global_propositional_subsumption,[status(thm)],[c_12108,c_38]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_44186,plain,
% 11.66/1.97      ( u1_struct_0(sK3) = sK4
% 11.66/1.97      | r2_hidden(sK0(sK4,u1_struct_0(sK3)),sK4) = iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_44173,c_13342]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_44698,plain,
% 11.66/1.97      ( u1_struct_0(sK3) = sK4 ),
% 11.66/1.97      inference(global_propositional_subsumption,
% 11.66/1.97                [status(thm)],
% 11.66/1.97                [c_44197,c_41,c_35256,c_35262,c_44186]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_25,negated_conjecture,
% 11.66/1.97      ( v1_subset_1(sK4,u1_struct_0(sK3)) | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
% 11.66/1.97      inference(cnf_transformation,[],[f90]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1238,plain,
% 11.66/1.97      ( v1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
% 11.66/1.97      | r2_hidden(k3_yellow_0(sK3),sK4) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3831,plain,
% 11.66/1.97      ( v1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 11.66/1.97      inference(superposition,[status(thm)],[c_3825,c_1238]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_44830,plain,
% 11.66/1.97      ( v1_subset_1(sK4,sK4) = iProver_top ),
% 11.66/1.97      inference(demodulation,[status(thm)],[c_44698,c_3831]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_5,plain,
% 11.66/1.97      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 11.66/1.97      inference(cnf_transformation,[],[f63]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1258,plain,
% 11.66/1.97      ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
% 11.66/1.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_3,plain,
% 11.66/1.97      ( k2_subset_1(X0) = X0 ),
% 11.66/1.97      inference(cnf_transformation,[],[f61]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_1283,plain,
% 11.66/1.97      ( v1_subset_1(X0,X0) != iProver_top ),
% 11.66/1.97      inference(light_normalisation,[status(thm)],[c_1258,c_3]) ).
% 11.66/1.97  
% 11.66/1.97  cnf(c_46748,plain,
% 11.66/1.97      ( $false ),
% 11.66/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_44830,c_1283]) ).
% 11.66/1.97  
% 11.66/1.97  
% 11.66/1.97  % SZS output end CNFRefutation for theBenchmark.p
% 11.66/1.97  
% 11.66/1.97  ------                               Statistics
% 11.66/1.97  
% 11.66/1.97  ------ Selected
% 11.66/1.97  
% 11.66/1.97  total_time:                             1.494
% 11.66/1.97  
%------------------------------------------------------------------------------
