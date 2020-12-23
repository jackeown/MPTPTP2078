%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:55 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 528 expanded)
%              Number of clauses        :   63 ( 149 expanded)
%              Number of leaves         :   22 ( 127 expanded)
%              Depth                    :   15
%              Number of atoms          :  370 (1670 expanded)
%              Number of equality atoms :  119 ( 478 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK4),X0)
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK3)
          & v1_subset_1(k6_domain_1(sK3,X1),sK3)
          & m1_subset_1(X1,sK3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( v1_zfmisc_1(sK3)
    & v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    & m1_subset_1(sK4,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f46,f45])).

fof(f72,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f83,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f81,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f78])).

fof(f82,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f81])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f67,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1402,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_428,plain,
    ( v1_xboole_0(X0)
    | k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_429,plain,
    ( v1_xboole_0(sK3)
    | k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_431,plain,
    ( k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_23])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1397,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2371,plain,
    ( sK4 = X0
    | r2_hidden(X0,k6_domain_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_1397])).

cnf(c_2841,plain,
    ( sK1(k6_domain_1(sK3,sK4),X0) = sK4
    | r1_tarski(k6_domain_1(sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_2371])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_131,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_11,c_9])).

cnf(c_132,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_20,negated_conjecture,
    ( v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_366,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X1 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_132,c_20])).

cnf(c_367,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | sK3 = X0 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_1392,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_3308,plain,
    ( k6_domain_1(sK3,sK4) = sK3
    | sK1(k6_domain_1(sK3,sK4),sK3) = sK4
    | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_1392])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_58,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_61,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_327,plain,
    ( l1_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_328,plain,
    ( l1_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_338,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_328])).

cnf(c_339,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_1393,plain,
    ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_18,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_347,plain,
    ( k2_yellow_1(X0) != X1
    | u1_struct_0(X1) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_328])).

cnf(c_348,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_1412,plain,
    ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_348,c_18])).

cnf(c_1421,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1393,c_18,c_1412])).

cnf(c_1495,plain,
    ( ~ v1_subset_1(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1421])).

cnf(c_1497,plain,
    ( ~ v1_subset_1(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1060,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1555,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    | X0 != k6_domain_1(sK3,sK4)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_1557,plain,
    ( ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    | v1_subset_1(sK3,sK3)
    | sK3 != k6_domain_1(sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_1642,plain,
    ( ~ r1_tarski(k6_domain_1(sK3,sK4),sK3)
    | v1_xboole_0(k6_domain_1(sK3,sK4))
    | sK3 = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1645,plain,
    ( sK3 = k6_domain_1(sK3,sK4)
    | r1_tarski(k6_domain_1(sK3,sK4),sK3) != iProver_top
    | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_1398,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1898,plain,
    ( r2_hidden(sK4,k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_1398])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1404,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2049,plain,
    ( v1_xboole_0(k6_domain_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_1404])).

cnf(c_2864,plain,
    ( sK1(k6_domain_1(sK3,sK4),sK3) = sK4
    | r1_tarski(k6_domain_1(sK3,sK4),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_3342,plain,
    ( sK1(k6_domain_1(sK3,sK4),sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3308,c_21,c_58,c_61,c_1497,c_1557,c_1645,c_2049,c_2864])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1403,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3346,plain,
    ( r1_tarski(k6_domain_1(sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3342,c_1403])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_436,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_437,plain,
    ( r2_hidden(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_438,plain,
    ( r2_hidden(sK4,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_24,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3346,c_2049,c_1645,c_1557,c_1497,c_438,c_61,c_58,c_21,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.91/1.10  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.10  
% 1.91/1.10  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.91/1.10  
% 1.91/1.10  ------  iProver source info
% 1.91/1.10  
% 1.91/1.10  git: date: 2020-06-30 10:37:57 +0100
% 1.91/1.10  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.91/1.10  git: non_committed_changes: false
% 1.91/1.10  git: last_make_outside_of_git: false
% 1.91/1.10  
% 1.91/1.10  ------ 
% 1.91/1.10  
% 1.91/1.10  ------ Input Options
% 1.91/1.10  
% 1.91/1.10  --out_options                           all
% 1.91/1.10  --tptp_safe_out                         true
% 1.91/1.10  --problem_path                          ""
% 1.91/1.10  --include_path                          ""
% 1.91/1.10  --clausifier                            res/vclausify_rel
% 1.91/1.10  --clausifier_options                    --mode clausify
% 1.91/1.10  --stdin                                 false
% 1.91/1.10  --stats_out                             all
% 1.91/1.10  
% 1.91/1.10  ------ General Options
% 1.91/1.10  
% 1.91/1.10  --fof                                   false
% 1.91/1.10  --time_out_real                         305.
% 1.91/1.10  --time_out_virtual                      -1.
% 1.91/1.10  --symbol_type_check                     false
% 1.91/1.10  --clausify_out                          false
% 1.91/1.10  --sig_cnt_out                           false
% 1.91/1.10  --trig_cnt_out                          false
% 1.91/1.10  --trig_cnt_out_tolerance                1.
% 1.91/1.10  --trig_cnt_out_sk_spl                   false
% 1.91/1.10  --abstr_cl_out                          false
% 1.91/1.10  
% 1.91/1.10  ------ Global Options
% 1.91/1.10  
% 1.91/1.10  --schedule                              default
% 1.91/1.10  --add_important_lit                     false
% 1.91/1.10  --prop_solver_per_cl                    1000
% 1.91/1.10  --min_unsat_core                        false
% 1.91/1.10  --soft_assumptions                      false
% 1.91/1.10  --soft_lemma_size                       3
% 1.91/1.10  --prop_impl_unit_size                   0
% 1.91/1.10  --prop_impl_unit                        []
% 1.91/1.10  --share_sel_clauses                     true
% 1.91/1.10  --reset_solvers                         false
% 1.91/1.10  --bc_imp_inh                            [conj_cone]
% 1.91/1.10  --conj_cone_tolerance                   3.
% 1.91/1.10  --extra_neg_conj                        none
% 1.91/1.10  --large_theory_mode                     true
% 1.91/1.10  --prolific_symb_bound                   200
% 1.91/1.10  --lt_threshold                          2000
% 1.91/1.10  --clause_weak_htbl                      true
% 1.91/1.10  --gc_record_bc_elim                     false
% 1.91/1.10  
% 1.91/1.10  ------ Preprocessing Options
% 1.91/1.10  
% 1.91/1.10  --preprocessing_flag                    true
% 1.91/1.10  --time_out_prep_mult                    0.1
% 1.91/1.10  --splitting_mode                        input
% 1.91/1.10  --splitting_grd                         true
% 1.91/1.10  --splitting_cvd                         false
% 1.91/1.10  --splitting_cvd_svl                     false
% 1.91/1.10  --splitting_nvd                         32
% 1.91/1.10  --sub_typing                            true
% 1.91/1.10  --prep_gs_sim                           true
% 1.91/1.10  --prep_unflatten                        true
% 1.91/1.10  --prep_res_sim                          true
% 1.91/1.10  --prep_upred                            true
% 1.91/1.10  --prep_sem_filter                       exhaustive
% 1.91/1.10  --prep_sem_filter_out                   false
% 1.91/1.10  --pred_elim                             true
% 1.91/1.10  --res_sim_input                         true
% 1.91/1.10  --eq_ax_congr_red                       true
% 1.91/1.10  --pure_diseq_elim                       true
% 1.91/1.10  --brand_transform                       false
% 1.91/1.10  --non_eq_to_eq                          false
% 1.91/1.10  --prep_def_merge                        true
% 1.91/1.10  --prep_def_merge_prop_impl              false
% 1.91/1.10  --prep_def_merge_mbd                    true
% 1.91/1.10  --prep_def_merge_tr_red                 false
% 1.91/1.10  --prep_def_merge_tr_cl                  false
% 1.91/1.10  --smt_preprocessing                     true
% 1.91/1.10  --smt_ac_axioms                         fast
% 1.91/1.10  --preprocessed_out                      false
% 1.91/1.10  --preprocessed_stats                    false
% 1.91/1.10  
% 1.91/1.10  ------ Abstraction refinement Options
% 1.91/1.10  
% 1.91/1.10  --abstr_ref                             []
% 1.91/1.10  --abstr_ref_prep                        false
% 1.91/1.10  --abstr_ref_until_sat                   false
% 1.91/1.10  --abstr_ref_sig_restrict                funpre
% 1.91/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.10  --abstr_ref_under                       []
% 1.91/1.10  
% 1.91/1.10  ------ SAT Options
% 1.91/1.10  
% 1.91/1.10  --sat_mode                              false
% 1.91/1.10  --sat_fm_restart_options                ""
% 1.91/1.10  --sat_gr_def                            false
% 1.91/1.10  --sat_epr_types                         true
% 1.91/1.10  --sat_non_cyclic_types                  false
% 1.91/1.10  --sat_finite_models                     false
% 1.91/1.10  --sat_fm_lemmas                         false
% 1.91/1.10  --sat_fm_prep                           false
% 1.91/1.10  --sat_fm_uc_incr                        true
% 1.91/1.10  --sat_out_model                         small
% 1.91/1.10  --sat_out_clauses                       false
% 1.91/1.10  
% 1.91/1.10  ------ QBF Options
% 1.91/1.10  
% 1.91/1.10  --qbf_mode                              false
% 1.91/1.10  --qbf_elim_univ                         false
% 1.91/1.10  --qbf_dom_inst                          none
% 1.91/1.10  --qbf_dom_pre_inst                      false
% 1.91/1.10  --qbf_sk_in                             false
% 1.91/1.10  --qbf_pred_elim                         true
% 1.91/1.10  --qbf_split                             512
% 1.91/1.10  
% 1.91/1.10  ------ BMC1 Options
% 1.91/1.10  
% 1.91/1.10  --bmc1_incremental                      false
% 1.91/1.10  --bmc1_axioms                           reachable_all
% 1.91/1.10  --bmc1_min_bound                        0
% 1.91/1.10  --bmc1_max_bound                        -1
% 1.91/1.10  --bmc1_max_bound_default                -1
% 1.91/1.10  --bmc1_symbol_reachability              true
% 1.91/1.10  --bmc1_property_lemmas                  false
% 1.91/1.10  --bmc1_k_induction                      false
% 1.91/1.10  --bmc1_non_equiv_states                 false
% 1.91/1.10  --bmc1_deadlock                         false
% 1.91/1.10  --bmc1_ucm                              false
% 1.91/1.10  --bmc1_add_unsat_core                   none
% 1.91/1.10  --bmc1_unsat_core_children              false
% 1.91/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.10  --bmc1_out_stat                         full
% 1.91/1.10  --bmc1_ground_init                      false
% 1.91/1.10  --bmc1_pre_inst_next_state              false
% 1.91/1.10  --bmc1_pre_inst_state                   false
% 1.91/1.10  --bmc1_pre_inst_reach_state             false
% 1.91/1.10  --bmc1_out_unsat_core                   false
% 1.91/1.10  --bmc1_aig_witness_out                  false
% 1.91/1.10  --bmc1_verbose                          false
% 1.91/1.10  --bmc1_dump_clauses_tptp                false
% 1.91/1.10  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.10  --bmc1_dump_file                        -
% 1.91/1.10  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.10  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.10  --bmc1_ucm_extend_mode                  1
% 1.91/1.10  --bmc1_ucm_init_mode                    2
% 1.91/1.10  --bmc1_ucm_cone_mode                    none
% 1.91/1.10  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.10  --bmc1_ucm_relax_model                  4
% 1.91/1.10  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.10  --bmc1_ucm_layered_model                none
% 1.91/1.10  --bmc1_ucm_max_lemma_size               10
% 1.91/1.10  
% 1.91/1.10  ------ AIG Options
% 1.91/1.10  
% 1.91/1.10  --aig_mode                              false
% 1.91/1.10  
% 1.91/1.10  ------ Instantiation Options
% 1.91/1.10  
% 1.91/1.10  --instantiation_flag                    true
% 1.91/1.10  --inst_sos_flag                         false
% 1.91/1.10  --inst_sos_phase                        true
% 1.91/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.10  --inst_lit_sel_side                     num_symb
% 1.91/1.10  --inst_solver_per_active                1400
% 1.91/1.10  --inst_solver_calls_frac                1.
% 1.91/1.10  --inst_passive_queue_type               priority_queues
% 1.91/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.10  --inst_passive_queues_freq              [25;2]
% 1.91/1.10  --inst_dismatching                      true
% 1.91/1.10  --inst_eager_unprocessed_to_passive     true
% 1.91/1.10  --inst_prop_sim_given                   true
% 1.91/1.10  --inst_prop_sim_new                     false
% 1.91/1.10  --inst_subs_new                         false
% 1.91/1.10  --inst_eq_res_simp                      false
% 1.91/1.10  --inst_subs_given                       false
% 1.91/1.10  --inst_orphan_elimination               true
% 1.91/1.10  --inst_learning_loop_flag               true
% 1.91/1.10  --inst_learning_start                   3000
% 1.91/1.10  --inst_learning_factor                  2
% 1.91/1.10  --inst_start_prop_sim_after_learn       3
% 1.91/1.10  --inst_sel_renew                        solver
% 1.91/1.10  --inst_lit_activity_flag                true
% 1.91/1.10  --inst_restr_to_given                   false
% 1.91/1.10  --inst_activity_threshold               500
% 1.91/1.10  --inst_out_proof                        true
% 1.91/1.10  
% 1.91/1.10  ------ Resolution Options
% 1.91/1.10  
% 1.91/1.10  --resolution_flag                       true
% 1.91/1.10  --res_lit_sel                           adaptive
% 1.91/1.10  --res_lit_sel_side                      none
% 1.91/1.10  --res_ordering                          kbo
% 1.91/1.10  --res_to_prop_solver                    active
% 1.91/1.10  --res_prop_simpl_new                    false
% 1.91/1.10  --res_prop_simpl_given                  true
% 1.91/1.10  --res_passive_queue_type                priority_queues
% 1.91/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.10  --res_passive_queues_freq               [15;5]
% 1.91/1.10  --res_forward_subs                      full
% 1.91/1.10  --res_backward_subs                     full
% 1.91/1.10  --res_forward_subs_resolution           true
% 1.91/1.10  --res_backward_subs_resolution          true
% 1.91/1.10  --res_orphan_elimination                true
% 1.91/1.10  --res_time_limit                        2.
% 1.91/1.10  --res_out_proof                         true
% 1.91/1.10  
% 1.91/1.10  ------ Superposition Options
% 1.91/1.10  
% 1.91/1.10  --superposition_flag                    true
% 1.91/1.10  --sup_passive_queue_type                priority_queues
% 1.91/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.10  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.10  --demod_completeness_check              fast
% 1.91/1.10  --demod_use_ground                      true
% 1.91/1.10  --sup_to_prop_solver                    passive
% 1.91/1.10  --sup_prop_simpl_new                    true
% 1.91/1.10  --sup_prop_simpl_given                  true
% 1.91/1.10  --sup_fun_splitting                     false
% 1.91/1.10  --sup_smt_interval                      50000
% 1.91/1.10  
% 1.91/1.10  ------ Superposition Simplification Setup
% 1.91/1.10  
% 1.91/1.10  --sup_indices_passive                   []
% 1.91/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.10  --sup_full_bw                           [BwDemod]
% 1.91/1.10  --sup_immed_triv                        [TrivRules]
% 1.91/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.10  --sup_immed_bw_main                     []
% 1.91/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.10  
% 1.91/1.10  ------ Combination Options
% 1.91/1.10  
% 1.91/1.10  --comb_res_mult                         3
% 1.91/1.10  --comb_sup_mult                         2
% 1.91/1.10  --comb_inst_mult                        10
% 1.91/1.10  
% 1.91/1.10  ------ Debug Options
% 1.91/1.10  
% 1.91/1.10  --dbg_backtrace                         false
% 1.91/1.10  --dbg_dump_prop_clauses                 false
% 1.91/1.10  --dbg_dump_prop_clauses_file            -
% 1.91/1.10  --dbg_out_stat                          false
% 1.91/1.10  ------ Parsing...
% 1.91/1.10  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/1.10  
% 1.91/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.91/1.10  
% 1.91/1.10  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/1.10  
% 1.91/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/1.10  ------ Proving...
% 1.91/1.10  ------ Problem Properties 
% 1.91/1.10  
% 1.91/1.10  
% 1.91/1.10  clauses                                 21
% 1.91/1.10  conjectures                             2
% 1.91/1.10  EPR                                     6
% 1.91/1.10  Horn                                    15
% 1.91/1.10  unary                                   8
% 1.91/1.10  binary                                  6
% 1.91/1.10  lits                                    41
% 1.91/1.10  lits eq                                 11
% 1.91/1.10  fd_pure                                 0
% 1.91/1.10  fd_pseudo                               0
% 1.91/1.10  fd_cond                                 1
% 1.91/1.10  fd_pseudo_cond                          2
% 1.91/1.10  AC symbols                              0
% 1.91/1.10  
% 1.91/1.10  ------ Schedule dynamic 5 is on 
% 1.91/1.10  
% 1.91/1.10  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/1.10  
% 1.91/1.10  
% 1.91/1.10  ------ 
% 1.91/1.10  Current options:
% 1.91/1.10  ------ 
% 1.91/1.10  
% 1.91/1.10  ------ Input Options
% 1.91/1.10  
% 1.91/1.10  --out_options                           all
% 1.91/1.10  --tptp_safe_out                         true
% 1.91/1.10  --problem_path                          ""
% 1.91/1.10  --include_path                          ""
% 1.91/1.10  --clausifier                            res/vclausify_rel
% 1.91/1.10  --clausifier_options                    --mode clausify
% 1.91/1.10  --stdin                                 false
% 1.91/1.10  --stats_out                             all
% 1.91/1.10  
% 1.91/1.10  ------ General Options
% 1.91/1.10  
% 1.91/1.10  --fof                                   false
% 1.91/1.10  --time_out_real                         305.
% 1.91/1.10  --time_out_virtual                      -1.
% 1.91/1.10  --symbol_type_check                     false
% 1.91/1.10  --clausify_out                          false
% 1.91/1.10  --sig_cnt_out                           false
% 1.91/1.10  --trig_cnt_out                          false
% 1.91/1.10  --trig_cnt_out_tolerance                1.
% 1.91/1.10  --trig_cnt_out_sk_spl                   false
% 1.91/1.10  --abstr_cl_out                          false
% 1.91/1.10  
% 1.91/1.10  ------ Global Options
% 1.91/1.10  
% 1.91/1.10  --schedule                              default
% 1.91/1.10  --add_important_lit                     false
% 1.91/1.10  --prop_solver_per_cl                    1000
% 1.91/1.10  --min_unsat_core                        false
% 1.91/1.10  --soft_assumptions                      false
% 1.91/1.10  --soft_lemma_size                       3
% 1.91/1.10  --prop_impl_unit_size                   0
% 1.91/1.10  --prop_impl_unit                        []
% 1.91/1.10  --share_sel_clauses                     true
% 1.91/1.10  --reset_solvers                         false
% 1.91/1.10  --bc_imp_inh                            [conj_cone]
% 1.91/1.10  --conj_cone_tolerance                   3.
% 1.91/1.10  --extra_neg_conj                        none
% 1.91/1.10  --large_theory_mode                     true
% 1.91/1.10  --prolific_symb_bound                   200
% 1.91/1.10  --lt_threshold                          2000
% 1.91/1.10  --clause_weak_htbl                      true
% 1.91/1.10  --gc_record_bc_elim                     false
% 1.91/1.10  
% 1.91/1.10  ------ Preprocessing Options
% 1.91/1.10  
% 1.91/1.10  --preprocessing_flag                    true
% 1.91/1.10  --time_out_prep_mult                    0.1
% 1.91/1.10  --splitting_mode                        input
% 1.91/1.10  --splitting_grd                         true
% 1.91/1.10  --splitting_cvd                         false
% 1.91/1.10  --splitting_cvd_svl                     false
% 1.91/1.10  --splitting_nvd                         32
% 1.91/1.10  --sub_typing                            true
% 1.91/1.10  --prep_gs_sim                           true
% 1.91/1.10  --prep_unflatten                        true
% 1.91/1.10  --prep_res_sim                          true
% 1.91/1.10  --prep_upred                            true
% 1.91/1.10  --prep_sem_filter                       exhaustive
% 1.91/1.10  --prep_sem_filter_out                   false
% 1.91/1.10  --pred_elim                             true
% 1.91/1.10  --res_sim_input                         true
% 1.91/1.10  --eq_ax_congr_red                       true
% 1.91/1.10  --pure_diseq_elim                       true
% 1.91/1.10  --brand_transform                       false
% 1.91/1.10  --non_eq_to_eq                          false
% 1.91/1.10  --prep_def_merge                        true
% 1.91/1.10  --prep_def_merge_prop_impl              false
% 1.91/1.10  --prep_def_merge_mbd                    true
% 1.91/1.10  --prep_def_merge_tr_red                 false
% 1.91/1.10  --prep_def_merge_tr_cl                  false
% 1.91/1.10  --smt_preprocessing                     true
% 1.91/1.10  --smt_ac_axioms                         fast
% 1.91/1.10  --preprocessed_out                      false
% 1.91/1.10  --preprocessed_stats                    false
% 1.91/1.10  
% 1.91/1.10  ------ Abstraction refinement Options
% 1.91/1.10  
% 1.91/1.10  --abstr_ref                             []
% 1.91/1.10  --abstr_ref_prep                        false
% 1.91/1.10  --abstr_ref_until_sat                   false
% 1.91/1.10  --abstr_ref_sig_restrict                funpre
% 1.91/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.10  --abstr_ref_under                       []
% 1.91/1.10  
% 1.91/1.10  ------ SAT Options
% 1.91/1.10  
% 1.91/1.10  --sat_mode                              false
% 1.91/1.10  --sat_fm_restart_options                ""
% 1.91/1.10  --sat_gr_def                            false
% 1.91/1.10  --sat_epr_types                         true
% 1.91/1.10  --sat_non_cyclic_types                  false
% 1.91/1.10  --sat_finite_models                     false
% 1.91/1.10  --sat_fm_lemmas                         false
% 1.91/1.10  --sat_fm_prep                           false
% 1.91/1.10  --sat_fm_uc_incr                        true
% 1.91/1.10  --sat_out_model                         small
% 1.91/1.10  --sat_out_clauses                       false
% 1.91/1.10  
% 1.91/1.10  ------ QBF Options
% 1.91/1.10  
% 1.91/1.10  --qbf_mode                              false
% 1.91/1.10  --qbf_elim_univ                         false
% 1.91/1.10  --qbf_dom_inst                          none
% 1.91/1.10  --qbf_dom_pre_inst                      false
% 1.91/1.10  --qbf_sk_in                             false
% 1.91/1.10  --qbf_pred_elim                         true
% 1.91/1.10  --qbf_split                             512
% 1.91/1.10  
% 1.91/1.10  ------ BMC1 Options
% 1.91/1.10  
% 1.91/1.10  --bmc1_incremental                      false
% 1.91/1.10  --bmc1_axioms                           reachable_all
% 1.91/1.10  --bmc1_min_bound                        0
% 1.91/1.10  --bmc1_max_bound                        -1
% 1.91/1.10  --bmc1_max_bound_default                -1
% 1.91/1.10  --bmc1_symbol_reachability              true
% 1.91/1.10  --bmc1_property_lemmas                  false
% 1.91/1.10  --bmc1_k_induction                      false
% 1.91/1.10  --bmc1_non_equiv_states                 false
% 1.91/1.10  --bmc1_deadlock                         false
% 1.91/1.10  --bmc1_ucm                              false
% 1.91/1.10  --bmc1_add_unsat_core                   none
% 1.91/1.10  --bmc1_unsat_core_children              false
% 1.91/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.10  --bmc1_out_stat                         full
% 1.91/1.10  --bmc1_ground_init                      false
% 1.91/1.10  --bmc1_pre_inst_next_state              false
% 1.91/1.10  --bmc1_pre_inst_state                   false
% 1.91/1.10  --bmc1_pre_inst_reach_state             false
% 1.91/1.10  --bmc1_out_unsat_core                   false
% 1.91/1.10  --bmc1_aig_witness_out                  false
% 1.91/1.10  --bmc1_verbose                          false
% 1.91/1.10  --bmc1_dump_clauses_tptp                false
% 1.91/1.10  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.10  --bmc1_dump_file                        -
% 1.91/1.10  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.10  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.10  --bmc1_ucm_extend_mode                  1
% 1.91/1.10  --bmc1_ucm_init_mode                    2
% 1.91/1.10  --bmc1_ucm_cone_mode                    none
% 1.91/1.10  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.10  --bmc1_ucm_relax_model                  4
% 1.91/1.10  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.10  --bmc1_ucm_layered_model                none
% 1.91/1.10  --bmc1_ucm_max_lemma_size               10
% 1.91/1.10  
% 1.91/1.10  ------ AIG Options
% 1.91/1.10  
% 1.91/1.10  --aig_mode                              false
% 1.91/1.10  
% 1.91/1.10  ------ Instantiation Options
% 1.91/1.10  
% 1.91/1.10  --instantiation_flag                    true
% 1.91/1.10  --inst_sos_flag                         false
% 1.91/1.10  --inst_sos_phase                        true
% 1.91/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.10  --inst_lit_sel_side                     none
% 1.91/1.10  --inst_solver_per_active                1400
% 1.91/1.10  --inst_solver_calls_frac                1.
% 1.91/1.10  --inst_passive_queue_type               priority_queues
% 1.91/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.10  --inst_passive_queues_freq              [25;2]
% 1.91/1.10  --inst_dismatching                      true
% 1.91/1.10  --inst_eager_unprocessed_to_passive     true
% 1.91/1.10  --inst_prop_sim_given                   true
% 1.91/1.10  --inst_prop_sim_new                     false
% 1.91/1.10  --inst_subs_new                         false
% 1.91/1.10  --inst_eq_res_simp                      false
% 1.91/1.10  --inst_subs_given                       false
% 1.91/1.10  --inst_orphan_elimination               true
% 1.91/1.10  --inst_learning_loop_flag               true
% 1.91/1.10  --inst_learning_start                   3000
% 1.91/1.10  --inst_learning_factor                  2
% 1.91/1.10  --inst_start_prop_sim_after_learn       3
% 1.91/1.10  --inst_sel_renew                        solver
% 1.91/1.10  --inst_lit_activity_flag                true
% 1.91/1.10  --inst_restr_to_given                   false
% 1.91/1.10  --inst_activity_threshold               500
% 1.91/1.10  --inst_out_proof                        true
% 1.91/1.10  
% 1.91/1.10  ------ Resolution Options
% 1.91/1.10  
% 1.91/1.10  --resolution_flag                       false
% 1.91/1.10  --res_lit_sel                           adaptive
% 1.91/1.10  --res_lit_sel_side                      none
% 1.91/1.10  --res_ordering                          kbo
% 1.91/1.10  --res_to_prop_solver                    active
% 1.91/1.10  --res_prop_simpl_new                    false
% 1.91/1.10  --res_prop_simpl_given                  true
% 1.91/1.10  --res_passive_queue_type                priority_queues
% 1.91/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.10  --res_passive_queues_freq               [15;5]
% 1.91/1.10  --res_forward_subs                      full
% 1.91/1.10  --res_backward_subs                     full
% 1.91/1.10  --res_forward_subs_resolution           true
% 1.91/1.10  --res_backward_subs_resolution          true
% 1.91/1.10  --res_orphan_elimination                true
% 1.91/1.10  --res_time_limit                        2.
% 1.91/1.10  --res_out_proof                         true
% 1.91/1.10  
% 1.91/1.10  ------ Superposition Options
% 1.91/1.10  
% 1.91/1.10  --superposition_flag                    true
% 1.91/1.10  --sup_passive_queue_type                priority_queues
% 1.91/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.10  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.10  --demod_completeness_check              fast
% 1.91/1.10  --demod_use_ground                      true
% 1.91/1.10  --sup_to_prop_solver                    passive
% 1.91/1.10  --sup_prop_simpl_new                    true
% 1.91/1.10  --sup_prop_simpl_given                  true
% 1.91/1.10  --sup_fun_splitting                     false
% 1.91/1.10  --sup_smt_interval                      50000
% 1.91/1.10  
% 1.91/1.10  ------ Superposition Simplification Setup
% 1.91/1.10  
% 1.91/1.10  --sup_indices_passive                   []
% 1.91/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.10  --sup_full_bw                           [BwDemod]
% 1.91/1.10  --sup_immed_triv                        [TrivRules]
% 1.91/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.10  --sup_immed_bw_main                     []
% 1.91/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.10  
% 1.91/1.10  ------ Combination Options
% 1.91/1.10  
% 1.91/1.10  --comb_res_mult                         3
% 1.91/1.10  --comb_sup_mult                         2
% 1.91/1.10  --comb_inst_mult                        10
% 1.91/1.10  
% 1.91/1.10  ------ Debug Options
% 1.91/1.10  
% 1.91/1.10  --dbg_backtrace                         false
% 1.91/1.10  --dbg_dump_prop_clauses                 false
% 1.91/1.10  --dbg_dump_prop_clauses_file            -
% 1.91/1.10  --dbg_out_stat                          false
% 1.91/1.10  
% 1.91/1.10  
% 1.91/1.10  
% 1.91/1.10  
% 1.91/1.10  ------ Proving...
% 1.91/1.10  
% 1.91/1.10  
% 1.91/1.10  % SZS status Theorem for theBenchmark.p
% 1.91/1.10  
% 1.91/1.10  % SZS output start CNFRefutation for theBenchmark.p
% 1.91/1.10  
% 1.91/1.10  fof(f2,axiom,(
% 1.91/1.10    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f19,plain,(
% 1.91/1.10    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.91/1.10    inference(ennf_transformation,[],[f2])).
% 1.91/1.10  
% 1.91/1.10  fof(f36,plain,(
% 1.91/1.10    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.10    inference(nnf_transformation,[],[f19])).
% 1.91/1.10  
% 1.91/1.10  fof(f37,plain,(
% 1.91/1.10    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.10    inference(rectify,[],[f36])).
% 1.91/1.10  
% 1.91/1.10  fof(f38,plain,(
% 1.91/1.10    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.91/1.10    introduced(choice_axiom,[])).
% 1.91/1.10  
% 1.91/1.10  fof(f39,plain,(
% 1.91/1.10    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 1.91/1.10  
% 1.91/1.10  fof(f51,plain,(
% 1.91/1.10    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f39])).
% 1.91/1.10  
% 1.91/1.10  fof(f12,axiom,(
% 1.91/1.10    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f26,plain,(
% 1.91/1.10    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.91/1.10    inference(ennf_transformation,[],[f12])).
% 1.91/1.10  
% 1.91/1.10  fof(f27,plain,(
% 1.91/1.10    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.91/1.10    inference(flattening,[],[f26])).
% 1.91/1.10  
% 1.91/1.10  fof(f66,plain,(
% 1.91/1.10    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f27])).
% 1.91/1.10  
% 1.91/1.10  fof(f4,axiom,(
% 1.91/1.10    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f57,plain,(
% 1.91/1.10    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f4])).
% 1.91/1.10  
% 1.91/1.10  fof(f5,axiom,(
% 1.91/1.10    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f58,plain,(
% 1.91/1.10    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f5])).
% 1.91/1.10  
% 1.91/1.10  fof(f75,plain,(
% 1.91/1.10    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.91/1.10    inference(definition_unfolding,[],[f57,f58])).
% 1.91/1.10  
% 1.91/1.10  fof(f80,plain,(
% 1.91/1.10    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.91/1.10    inference(definition_unfolding,[],[f66,f75])).
% 1.91/1.10  
% 1.91/1.10  fof(f16,conjecture,(
% 1.91/1.10    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f17,negated_conjecture,(
% 1.91/1.10    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.91/1.10    inference(negated_conjecture,[],[f16])).
% 1.91/1.10  
% 1.91/1.10  fof(f30,plain,(
% 1.91/1.10    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.91/1.10    inference(ennf_transformation,[],[f17])).
% 1.91/1.10  
% 1.91/1.10  fof(f31,plain,(
% 1.91/1.10    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.91/1.10    inference(flattening,[],[f30])).
% 1.91/1.10  
% 1.91/1.10  fof(f46,plain,(
% 1.91/1.10    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK4),X0) & m1_subset_1(sK4,X0))) )),
% 1.91/1.10    introduced(choice_axiom,[])).
% 1.91/1.10  
% 1.91/1.10  fof(f45,plain,(
% 1.91/1.10    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,X1),sK3) & m1_subset_1(X1,sK3)) & ~v1_xboole_0(sK3))),
% 1.91/1.10    introduced(choice_axiom,[])).
% 1.91/1.10  
% 1.91/1.10  fof(f47,plain,(
% 1.91/1.10    (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,sK4),sK3) & m1_subset_1(sK4,sK3)) & ~v1_xboole_0(sK3)),
% 1.91/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f46,f45])).
% 1.91/1.10  
% 1.91/1.10  fof(f72,plain,(
% 1.91/1.10    m1_subset_1(sK4,sK3)),
% 1.91/1.10    inference(cnf_transformation,[],[f47])).
% 1.91/1.10  
% 1.91/1.10  fof(f71,plain,(
% 1.91/1.10    ~v1_xboole_0(sK3)),
% 1.91/1.10    inference(cnf_transformation,[],[f47])).
% 1.91/1.10  
% 1.91/1.10  fof(f3,axiom,(
% 1.91/1.10    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f40,plain,(
% 1.91/1.10    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.91/1.10    inference(nnf_transformation,[],[f3])).
% 1.91/1.10  
% 1.91/1.10  fof(f41,plain,(
% 1.91/1.10    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.91/1.10    inference(rectify,[],[f40])).
% 1.91/1.10  
% 1.91/1.10  fof(f42,plain,(
% 1.91/1.10    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.91/1.10    introduced(choice_axiom,[])).
% 1.91/1.10  
% 1.91/1.10  fof(f43,plain,(
% 1.91/1.10    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.91/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 1.91/1.10  
% 1.91/1.10  fof(f53,plain,(
% 1.91/1.10    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.91/1.10    inference(cnf_transformation,[],[f43])).
% 1.91/1.10  
% 1.91/1.10  fof(f79,plain,(
% 1.91/1.10    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.91/1.10    inference(definition_unfolding,[],[f53,f75])).
% 1.91/1.10  
% 1.91/1.10  fof(f83,plain,(
% 1.91/1.10    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 1.91/1.10    inference(equality_resolution,[],[f79])).
% 1.91/1.10  
% 1.91/1.10  fof(f15,axiom,(
% 1.91/1.10    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f28,plain,(
% 1.91/1.10    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.91/1.10    inference(ennf_transformation,[],[f15])).
% 1.91/1.10  
% 1.91/1.10  fof(f29,plain,(
% 1.91/1.10    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.91/1.10    inference(flattening,[],[f28])).
% 1.91/1.10  
% 1.91/1.10  fof(f70,plain,(
% 1.91/1.10    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f29])).
% 1.91/1.10  
% 1.91/1.10  fof(f8,axiom,(
% 1.91/1.10    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f44,plain,(
% 1.91/1.10    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.91/1.10    inference(nnf_transformation,[],[f8])).
% 1.91/1.10  
% 1.91/1.10  fof(f62,plain,(
% 1.91/1.10    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f44])).
% 1.91/1.10  
% 1.91/1.10  fof(f6,axiom,(
% 1.91/1.10    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f20,plain,(
% 1.91/1.10    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.91/1.10    inference(ennf_transformation,[],[f6])).
% 1.91/1.10  
% 1.91/1.10  fof(f59,plain,(
% 1.91/1.10    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f20])).
% 1.91/1.10  
% 1.91/1.10  fof(f74,plain,(
% 1.91/1.10    v1_zfmisc_1(sK3)),
% 1.91/1.10    inference(cnf_transformation,[],[f47])).
% 1.91/1.10  
% 1.91/1.10  fof(f73,plain,(
% 1.91/1.10    v1_subset_1(k6_domain_1(sK3,sK4),sK3)),
% 1.91/1.10    inference(cnf_transformation,[],[f47])).
% 1.91/1.10  
% 1.91/1.10  fof(f54,plain,(
% 1.91/1.10    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.91/1.10    inference(cnf_transformation,[],[f43])).
% 1.91/1.10  
% 1.91/1.10  fof(f78,plain,(
% 1.91/1.10    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 1.91/1.10    inference(definition_unfolding,[],[f54,f75])).
% 1.91/1.10  
% 1.91/1.10  fof(f81,plain,(
% 1.91/1.10    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 1.91/1.10    inference(equality_resolution,[],[f78])).
% 1.91/1.10  
% 1.91/1.10  fof(f82,plain,(
% 1.91/1.10    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 1.91/1.10    inference(equality_resolution,[],[f81])).
% 1.91/1.10  
% 1.91/1.10  fof(f10,axiom,(
% 1.91/1.10    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f24,plain,(
% 1.91/1.10    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.91/1.10    inference(ennf_transformation,[],[f10])).
% 1.91/1.10  
% 1.91/1.10  fof(f64,plain,(
% 1.91/1.10    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f24])).
% 1.91/1.10  
% 1.91/1.10  fof(f11,axiom,(
% 1.91/1.10    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f25,plain,(
% 1.91/1.10    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.91/1.10    inference(ennf_transformation,[],[f11])).
% 1.91/1.10  
% 1.91/1.10  fof(f65,plain,(
% 1.91/1.10    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f25])).
% 1.91/1.10  
% 1.91/1.10  fof(f13,axiom,(
% 1.91/1.10    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f18,plain,(
% 1.91/1.10    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.91/1.10    inference(pure_predicate_removal,[],[f13])).
% 1.91/1.10  
% 1.91/1.10  fof(f67,plain,(
% 1.91/1.10    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.91/1.10    inference(cnf_transformation,[],[f18])).
% 1.91/1.10  
% 1.91/1.10  fof(f14,axiom,(
% 1.91/1.10    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f68,plain,(
% 1.91/1.10    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.91/1.10    inference(cnf_transformation,[],[f14])).
% 1.91/1.10  
% 1.91/1.10  fof(f9,axiom,(
% 1.91/1.10    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f23,plain,(
% 1.91/1.10    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.91/1.10    inference(ennf_transformation,[],[f9])).
% 1.91/1.10  
% 1.91/1.10  fof(f63,plain,(
% 1.91/1.10    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f23])).
% 1.91/1.10  
% 1.91/1.10  fof(f1,axiom,(
% 1.91/1.10    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f32,plain,(
% 1.91/1.10    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.10    inference(nnf_transformation,[],[f1])).
% 1.91/1.10  
% 1.91/1.10  fof(f33,plain,(
% 1.91/1.10    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.10    inference(rectify,[],[f32])).
% 1.91/1.10  
% 1.91/1.10  fof(f34,plain,(
% 1.91/1.10    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.91/1.10    introduced(choice_axiom,[])).
% 1.91/1.10  
% 1.91/1.10  fof(f35,plain,(
% 1.91/1.10    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 1.91/1.10  
% 1.91/1.10  fof(f48,plain,(
% 1.91/1.10    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f35])).
% 1.91/1.10  
% 1.91/1.10  fof(f52,plain,(
% 1.91/1.10    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f39])).
% 1.91/1.10  
% 1.91/1.10  fof(f7,axiom,(
% 1.91/1.10    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.91/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.10  
% 1.91/1.10  fof(f21,plain,(
% 1.91/1.10    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.91/1.10    inference(ennf_transformation,[],[f7])).
% 1.91/1.10  
% 1.91/1.10  fof(f22,plain,(
% 1.91/1.10    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.91/1.10    inference(flattening,[],[f21])).
% 1.91/1.10  
% 1.91/1.10  fof(f60,plain,(
% 1.91/1.10    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.91/1.10    inference(cnf_transformation,[],[f22])).
% 1.91/1.10  
% 1.91/1.10  cnf(c_3,plain,
% 1.91/1.10      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.91/1.10      inference(cnf_transformation,[],[f51]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_1402,plain,
% 1.91/1.10      ( r1_tarski(X0,X1) = iProver_top
% 1.91/1.10      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.91/1.10      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_16,plain,
% 1.91/1.10      ( ~ m1_subset_1(X0,X1)
% 1.91/1.10      | v1_xboole_0(X1)
% 1.91/1.10      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 1.91/1.10      inference(cnf_transformation,[],[f80]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_22,negated_conjecture,
% 1.91/1.10      ( m1_subset_1(sK4,sK3) ),
% 1.91/1.10      inference(cnf_transformation,[],[f72]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_428,plain,
% 1.91/1.10      ( v1_xboole_0(X0)
% 1.91/1.10      | k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
% 1.91/1.10      | sK4 != X1
% 1.91/1.10      | sK3 != X0 ),
% 1.91/1.10      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_429,plain,
% 1.91/1.10      ( v1_xboole_0(sK3)
% 1.91/1.10      | k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 1.91/1.10      inference(unflattening,[status(thm)],[c_428]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_23,negated_conjecture,
% 1.91/1.10      ( ~ v1_xboole_0(sK3) ),
% 1.91/1.10      inference(cnf_transformation,[],[f71]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_431,plain,
% 1.91/1.10      ( k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 1.91/1.10      inference(global_propositional_subsumption,
% 1.91/1.10                [status(thm)],
% 1.91/1.10                [c_429,c_23]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_8,plain,
% 1.91/1.10      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 1.91/1.10      inference(cnf_transformation,[],[f83]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_1397,plain,
% 1.91/1.10      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 1.91/1.10      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_2371,plain,
% 1.91/1.10      ( sK4 = X0 | r2_hidden(X0,k6_domain_1(sK3,sK4)) != iProver_top ),
% 1.91/1.10      inference(superposition,[status(thm)],[c_431,c_1397]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_2841,plain,
% 1.91/1.10      ( sK1(k6_domain_1(sK3,sK4),X0) = sK4
% 1.91/1.10      | r1_tarski(k6_domain_1(sK3,sK4),X0) = iProver_top ),
% 1.91/1.10      inference(superposition,[status(thm)],[c_1402,c_2371]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_19,plain,
% 1.91/1.10      ( ~ r1_tarski(X0,X1)
% 1.91/1.10      | ~ v1_zfmisc_1(X1)
% 1.91/1.10      | v1_xboole_0(X0)
% 1.91/1.10      | v1_xboole_0(X1)
% 1.91/1.10      | X1 = X0 ),
% 1.91/1.10      inference(cnf_transformation,[],[f70]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_11,plain,
% 1.91/1.10      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.91/1.10      inference(cnf_transformation,[],[f62]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_9,plain,
% 1.91/1.10      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.91/1.10      | ~ v1_xboole_0(X1)
% 1.91/1.10      | v1_xboole_0(X0) ),
% 1.91/1.10      inference(cnf_transformation,[],[f59]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_131,plain,
% 1.91/1.10      ( v1_xboole_0(X0)
% 1.91/1.10      | ~ v1_zfmisc_1(X1)
% 1.91/1.10      | ~ r1_tarski(X0,X1)
% 1.91/1.10      | X1 = X0 ),
% 1.91/1.10      inference(global_propositional_subsumption,
% 1.91/1.10                [status(thm)],
% 1.91/1.10                [c_19,c_11,c_9]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_132,plain,
% 1.91/1.10      ( ~ r1_tarski(X0,X1)
% 1.91/1.10      | ~ v1_zfmisc_1(X1)
% 1.91/1.10      | v1_xboole_0(X0)
% 1.91/1.10      | X1 = X0 ),
% 1.91/1.10      inference(renaming,[status(thm)],[c_131]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_20,negated_conjecture,
% 1.91/1.10      ( v1_zfmisc_1(sK3) ),
% 1.91/1.10      inference(cnf_transformation,[],[f74]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_366,plain,
% 1.91/1.10      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X1 = X0 | sK3 != X1 ),
% 1.91/1.10      inference(resolution_lifted,[status(thm)],[c_132,c_20]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_367,plain,
% 1.91/1.10      ( ~ r1_tarski(X0,sK3) | v1_xboole_0(X0) | sK3 = X0 ),
% 1.91/1.10      inference(unflattening,[status(thm)],[c_366]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_1392,plain,
% 1.91/1.10      ( sK3 = X0
% 1.91/1.10      | r1_tarski(X0,sK3) != iProver_top
% 1.91/1.10      | v1_xboole_0(X0) = iProver_top ),
% 1.91/1.10      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_3308,plain,
% 1.91/1.10      ( k6_domain_1(sK3,sK4) = sK3
% 1.91/1.10      | sK1(k6_domain_1(sK3,sK4),sK3) = sK4
% 1.91/1.10      | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 1.91/1.10      inference(superposition,[status(thm)],[c_2841,c_1392]) ).
% 1.91/1.10  
% 1.91/1.10  cnf(c_21,negated_conjecture,
% 1.91/1.10      ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
% 1.91/1.11      inference(cnf_transformation,[],[f73]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_58,plain,
% 1.91/1.11      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | sK3 = sK3 ),
% 1.91/1.11      inference(instantiation,[status(thm)],[c_8]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_7,plain,
% 1.91/1.11      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 1.91/1.11      inference(cnf_transformation,[],[f82]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_61,plain,
% 1.91/1.11      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
% 1.91/1.11      inference(instantiation,[status(thm)],[c_7]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_14,plain,
% 1.91/1.11      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 1.91/1.11      | ~ l1_struct_0(X0) ),
% 1.91/1.11      inference(cnf_transformation,[],[f64]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_15,plain,
% 1.91/1.11      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.91/1.11      inference(cnf_transformation,[],[f65]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_17,plain,
% 1.91/1.11      ( l1_orders_2(k2_yellow_1(X0)) ),
% 1.91/1.11      inference(cnf_transformation,[],[f67]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_327,plain,
% 1.91/1.11      ( l1_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 1.91/1.11      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_328,plain,
% 1.91/1.11      ( l1_struct_0(k2_yellow_1(X0)) ),
% 1.91/1.11      inference(unflattening,[status(thm)],[c_327]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_338,plain,
% 1.91/1.11      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 1.91/1.11      | k2_yellow_1(X1) != X0 ),
% 1.91/1.11      inference(resolution_lifted,[status(thm)],[c_14,c_328]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_339,plain,
% 1.91/1.11      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 1.91/1.11      inference(unflattening,[status(thm)],[c_338]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1393,plain,
% 1.91/1.11      ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 1.91/1.11      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_18,plain,
% 1.91/1.11      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 1.91/1.11      inference(cnf_transformation,[],[f68]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_13,plain,
% 1.91/1.11      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.91/1.11      inference(cnf_transformation,[],[f63]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_347,plain,
% 1.91/1.11      ( k2_yellow_1(X0) != X1 | u1_struct_0(X1) = k2_struct_0(X1) ),
% 1.91/1.11      inference(resolution_lifted,[status(thm)],[c_13,c_328]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_348,plain,
% 1.91/1.11      ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
% 1.91/1.11      inference(unflattening,[status(thm)],[c_347]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1412,plain,
% 1.91/1.11      ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
% 1.91/1.11      inference(light_normalisation,[status(thm)],[c_348,c_18]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1421,plain,
% 1.91/1.11      ( v1_subset_1(X0,X0) != iProver_top ),
% 1.91/1.11      inference(light_normalisation,[status(thm)],[c_1393,c_18,c_1412]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1495,plain,
% 1.91/1.11      ( ~ v1_subset_1(X0,X0) ),
% 1.91/1.11      inference(predicate_to_equality_rev,[status(thm)],[c_1421]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1497,plain,
% 1.91/1.11      ( ~ v1_subset_1(sK3,sK3) ),
% 1.91/1.11      inference(instantiation,[status(thm)],[c_1495]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1060,plain,
% 1.91/1.11      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.91/1.11      theory(equality) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1555,plain,
% 1.91/1.11      ( v1_subset_1(X0,X1)
% 1.91/1.11      | ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
% 1.91/1.11      | X0 != k6_domain_1(sK3,sK4)
% 1.91/1.11      | X1 != sK3 ),
% 1.91/1.11      inference(instantiation,[status(thm)],[c_1060]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1557,plain,
% 1.91/1.11      ( ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
% 1.91/1.11      | v1_subset_1(sK3,sK3)
% 1.91/1.11      | sK3 != k6_domain_1(sK3,sK4)
% 1.91/1.11      | sK3 != sK3 ),
% 1.91/1.11      inference(instantiation,[status(thm)],[c_1555]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1642,plain,
% 1.91/1.11      ( ~ r1_tarski(k6_domain_1(sK3,sK4),sK3)
% 1.91/1.11      | v1_xboole_0(k6_domain_1(sK3,sK4))
% 1.91/1.11      | sK3 = k6_domain_1(sK3,sK4) ),
% 1.91/1.11      inference(instantiation,[status(thm)],[c_367]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1645,plain,
% 1.91/1.11      ( sK3 = k6_domain_1(sK3,sK4)
% 1.91/1.11      | r1_tarski(k6_domain_1(sK3,sK4),sK3) != iProver_top
% 1.91/1.11      | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 1.91/1.11      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1398,plain,
% 1.91/1.11      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 1.91/1.11      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1898,plain,
% 1.91/1.11      ( r2_hidden(sK4,k6_domain_1(sK3,sK4)) = iProver_top ),
% 1.91/1.11      inference(superposition,[status(thm)],[c_431,c_1398]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1,plain,
% 1.91/1.11      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.91/1.11      inference(cnf_transformation,[],[f48]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1404,plain,
% 1.91/1.11      ( r2_hidden(X0,X1) != iProver_top
% 1.91/1.11      | v1_xboole_0(X1) != iProver_top ),
% 1.91/1.11      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_2049,plain,
% 1.91/1.11      ( v1_xboole_0(k6_domain_1(sK3,sK4)) != iProver_top ),
% 1.91/1.11      inference(superposition,[status(thm)],[c_1898,c_1404]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_2864,plain,
% 1.91/1.11      ( sK1(k6_domain_1(sK3,sK4),sK3) = sK4
% 1.91/1.11      | r1_tarski(k6_domain_1(sK3,sK4),sK3) = iProver_top ),
% 1.91/1.11      inference(instantiation,[status(thm)],[c_2841]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_3342,plain,
% 1.91/1.11      ( sK1(k6_domain_1(sK3,sK4),sK3) = sK4 ),
% 1.91/1.11      inference(global_propositional_subsumption,
% 1.91/1.11                [status(thm)],
% 1.91/1.11                [c_3308,c_21,c_58,c_61,c_1497,c_1557,c_1645,c_2049,
% 1.91/1.11                 c_2864]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_2,plain,
% 1.91/1.11      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 1.91/1.11      inference(cnf_transformation,[],[f52]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_1403,plain,
% 1.91/1.11      ( r1_tarski(X0,X1) = iProver_top
% 1.91/1.11      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 1.91/1.11      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_3346,plain,
% 1.91/1.11      ( r1_tarski(k6_domain_1(sK3,sK4),sK3) = iProver_top
% 1.91/1.11      | r2_hidden(sK4,sK3) != iProver_top ),
% 1.91/1.11      inference(superposition,[status(thm)],[c_3342,c_1403]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_10,plain,
% 1.91/1.11      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.91/1.11      inference(cnf_transformation,[],[f60]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_436,plain,
% 1.91/1.11      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | sK4 != X0 | sK3 != X1 ),
% 1.91/1.11      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_437,plain,
% 1.91/1.11      ( r2_hidden(sK4,sK3) | v1_xboole_0(sK3) ),
% 1.91/1.11      inference(unflattening,[status(thm)],[c_436]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_438,plain,
% 1.91/1.11      ( r2_hidden(sK4,sK3) = iProver_top
% 1.91/1.11      | v1_xboole_0(sK3) = iProver_top ),
% 1.91/1.11      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(c_24,plain,
% 1.91/1.11      ( v1_xboole_0(sK3) != iProver_top ),
% 1.91/1.11      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.91/1.11  
% 1.91/1.11  cnf(contradiction,plain,
% 1.91/1.11      ( $false ),
% 1.91/1.11      inference(minisat,
% 1.91/1.11                [status(thm)],
% 1.91/1.11                [c_3346,c_2049,c_1645,c_1557,c_1497,c_438,c_61,c_58,c_21,
% 1.91/1.11                 c_24]) ).
% 1.91/1.11  
% 1.91/1.11  
% 1.91/1.11  % SZS output end CNFRefutation for theBenchmark.p
% 1.91/1.11  
% 1.91/1.11  ------                               Statistics
% 1.91/1.11  
% 1.91/1.11  ------ General
% 1.91/1.11  
% 1.91/1.11  abstr_ref_over_cycles:                  0
% 1.91/1.11  abstr_ref_under_cycles:                 0
% 1.91/1.11  gc_basic_clause_elim:                   0
% 1.91/1.11  forced_gc_time:                         0
% 1.91/1.11  parsing_time:                           0.006
% 1.91/1.11  unif_index_cands_time:                  0.
% 1.91/1.11  unif_index_add_time:                    0.
% 1.91/1.11  orderings_time:                         0.
% 1.91/1.11  out_proof_time:                         0.03
% 1.91/1.11  total_time:                             0.164
% 1.91/1.11  num_of_symbols:                         50
% 1.91/1.11  num_of_terms:                           2380
% 1.91/1.11  
% 1.91/1.11  ------ Preprocessing
% 1.91/1.11  
% 1.91/1.11  num_of_splits:                          0
% 1.91/1.11  num_of_split_atoms:                     0
% 1.91/1.11  num_of_reused_defs:                     0
% 1.91/1.11  num_eq_ax_congr_red:                    28
% 1.91/1.11  num_of_sem_filtered_clauses:            1
% 1.91/1.11  num_of_subtypes:                        0
% 1.91/1.11  monotx_restored_types:                  0
% 1.91/1.11  sat_num_of_epr_types:                   0
% 1.91/1.11  sat_num_of_non_cyclic_types:            0
% 1.91/1.11  sat_guarded_non_collapsed_types:        0
% 1.91/1.11  num_pure_diseq_elim:                    0
% 1.91/1.11  simp_replaced_by:                       0
% 1.91/1.11  res_preprocessed:                       108
% 1.91/1.11  prep_upred:                             0
% 1.91/1.11  prep_unflattend:                        41
% 1.91/1.11  smt_new_axioms:                         0
% 1.91/1.11  pred_elim_cands:                        4
% 1.91/1.11  pred_elim:                              4
% 1.91/1.11  pred_elim_cl:                           3
% 1.91/1.11  pred_elim_cycles:                       9
% 1.91/1.11  merged_defs:                            2
% 1.91/1.11  merged_defs_ncl:                        0
% 1.91/1.11  bin_hyper_res:                          3
% 1.91/1.11  prep_cycles:                            4
% 1.91/1.11  pred_elim_time:                         0.008
% 1.91/1.11  splitting_time:                         0.
% 1.91/1.11  sem_filter_time:                        0.
% 1.91/1.11  monotx_time:                            0.
% 1.91/1.11  subtype_inf_time:                       0.
% 1.91/1.11  
% 1.91/1.11  ------ Problem properties
% 1.91/1.11  
% 1.91/1.11  clauses:                                21
% 1.91/1.11  conjectures:                            2
% 1.91/1.11  epr:                                    6
% 1.91/1.11  horn:                                   15
% 1.91/1.11  ground:                                 4
% 1.91/1.11  unary:                                  8
% 1.91/1.11  binary:                                 6
% 1.91/1.11  lits:                                   41
% 1.91/1.11  lits_eq:                                11
% 1.91/1.11  fd_pure:                                0
% 1.91/1.11  fd_pseudo:                              0
% 1.91/1.11  fd_cond:                                1
% 1.91/1.11  fd_pseudo_cond:                         2
% 1.91/1.11  ac_symbols:                             0
% 1.91/1.11  
% 1.91/1.11  ------ Propositional Solver
% 1.91/1.11  
% 1.91/1.11  prop_solver_calls:                      26
% 1.91/1.11  prop_fast_solver_calls:                 643
% 1.91/1.11  smt_solver_calls:                       0
% 1.91/1.11  smt_fast_solver_calls:                  0
% 1.91/1.11  prop_num_of_clauses:                    1106
% 1.91/1.11  prop_preprocess_simplified:             5091
% 1.91/1.11  prop_fo_subsumed:                       6
% 1.91/1.11  prop_solver_time:                       0.
% 1.91/1.11  smt_solver_time:                        0.
% 1.91/1.11  smt_fast_solver_time:                   0.
% 1.91/1.11  prop_fast_solver_time:                  0.
% 1.91/1.11  prop_unsat_core_time:                   0.
% 1.91/1.11  
% 1.91/1.11  ------ QBF
% 1.91/1.11  
% 1.91/1.11  qbf_q_res:                              0
% 1.91/1.11  qbf_num_tautologies:                    0
% 1.91/1.11  qbf_prep_cycles:                        0
% 1.91/1.11  
% 1.91/1.11  ------ BMC1
% 1.91/1.11  
% 1.91/1.11  bmc1_current_bound:                     -1
% 1.91/1.11  bmc1_last_solved_bound:                 -1
% 1.91/1.11  bmc1_unsat_core_size:                   -1
% 1.91/1.11  bmc1_unsat_core_parents_size:           -1
% 1.91/1.11  bmc1_merge_next_fun:                    0
% 1.91/1.11  bmc1_unsat_core_clauses_time:           0.
% 1.91/1.11  
% 1.91/1.11  ------ Instantiation
% 1.91/1.11  
% 1.91/1.11  inst_num_of_clauses:                    313
% 1.91/1.11  inst_num_in_passive:                    180
% 1.91/1.11  inst_num_in_active:                     130
% 1.91/1.11  inst_num_in_unprocessed:                3
% 1.91/1.11  inst_num_of_loops:                      140
% 1.91/1.11  inst_num_of_learning_restarts:          0
% 1.91/1.11  inst_num_moves_active_passive:          9
% 1.91/1.11  inst_lit_activity:                      0
% 1.91/1.11  inst_lit_activity_moves:                0
% 1.91/1.11  inst_num_tautologies:                   0
% 1.91/1.11  inst_num_prop_implied:                  0
% 1.91/1.11  inst_num_existing_simplified:           0
% 1.91/1.11  inst_num_eq_res_simplified:             0
% 1.91/1.11  inst_num_child_elim:                    0
% 1.91/1.11  inst_num_of_dismatching_blockings:      63
% 1.91/1.11  inst_num_of_non_proper_insts:           266
% 1.91/1.11  inst_num_of_duplicates:                 0
% 1.91/1.11  inst_inst_num_from_inst_to_res:         0
% 1.91/1.11  inst_dismatching_checking_time:         0.
% 1.91/1.11  
% 1.91/1.11  ------ Resolution
% 1.91/1.11  
% 1.91/1.11  res_num_of_clauses:                     0
% 1.91/1.11  res_num_in_passive:                     0
% 1.91/1.11  res_num_in_active:                      0
% 1.91/1.11  res_num_of_loops:                       112
% 1.91/1.11  res_forward_subset_subsumed:            15
% 1.91/1.11  res_backward_subset_subsumed:           0
% 1.91/1.11  res_forward_subsumed:                   2
% 1.91/1.11  res_backward_subsumed:                  0
% 1.91/1.11  res_forward_subsumption_resolution:     0
% 1.91/1.11  res_backward_subsumption_resolution:    0
% 1.91/1.11  res_clause_to_clause_subsumption:       99
% 1.91/1.11  res_orphan_elimination:                 0
% 1.91/1.11  res_tautology_del:                      17
% 1.91/1.11  res_num_eq_res_simplified:              0
% 1.91/1.11  res_num_sel_changes:                    0
% 1.91/1.11  res_moves_from_active_to_pass:          0
% 1.91/1.11  
% 1.91/1.11  ------ Superposition
% 1.91/1.11  
% 1.91/1.11  sup_time_total:                         0.
% 1.91/1.11  sup_time_generating:                    0.
% 1.91/1.11  sup_time_sim_full:                      0.
% 1.91/1.11  sup_time_sim_immed:                     0.
% 1.91/1.11  
% 1.91/1.11  sup_num_of_clauses:                     40
% 1.91/1.11  sup_num_in_active:                      28
% 1.91/1.11  sup_num_in_passive:                     12
% 1.91/1.11  sup_num_of_loops:                       27
% 1.91/1.11  sup_fw_superposition:                   12
% 1.91/1.11  sup_bw_superposition:                   15
% 1.91/1.11  sup_immediate_simplified:               2
% 1.91/1.11  sup_given_eliminated:                   0
% 1.91/1.11  comparisons_done:                       0
% 1.91/1.11  comparisons_avoided:                    2
% 1.91/1.11  
% 1.91/1.11  ------ Simplifications
% 1.91/1.11  
% 1.91/1.11  
% 1.91/1.11  sim_fw_subset_subsumed:                 2
% 1.91/1.11  sim_bw_subset_subsumed:                 0
% 1.91/1.11  sim_fw_subsumed:                        0
% 1.91/1.11  sim_bw_subsumed:                        0
% 1.91/1.11  sim_fw_subsumption_res:                 0
% 1.91/1.11  sim_bw_subsumption_res:                 0
% 1.91/1.11  sim_tautology_del:                      2
% 1.91/1.11  sim_eq_tautology_del:                   2
% 1.91/1.11  sim_eq_res_simp:                        0
% 1.91/1.11  sim_fw_demodulated:                     0
% 1.91/1.11  sim_bw_demodulated:                     0
% 1.91/1.11  sim_light_normalised:                   2
% 1.91/1.11  sim_joinable_taut:                      0
% 1.91/1.11  sim_joinable_simp:                      0
% 1.91/1.11  sim_ac_normalised:                      0
% 1.91/1.11  sim_smt_subsumption:                    0
% 1.91/1.11  
%------------------------------------------------------------------------------
