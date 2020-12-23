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
% DateTime   : Thu Dec  3 12:25:01 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 253 expanded)
%              Number of clauses        :   53 (  74 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  374 ( 868 expanded)
%              Number of equality atoms :  115 ( 137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK3),X0)
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK2)
          & v1_subset_1(k6_domain_1(sK2,X1),sK2)
          & m1_subset_1(X1,sK2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( v1_zfmisc_1(sK2)
    & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    & m1_subset_1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f41,f40])).

fof(f67,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f85,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f79])).

fof(f86,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f85])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_737,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_740,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1386,plain,
    ( r2_hidden(sK3,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_740])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_887,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | r2_hidden(sK3,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_888,plain,
    ( m1_subset_1(sK3,sK2) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_887])).

cnf(c_1547,plain,
    ( r2_hidden(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1386,c_24,c_25,c_888])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_254,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_255,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_748,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1541,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_255,c_748])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1542,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1541,c_9])).

cnf(c_2290,plain,
    ( r2_hidden(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1542])).

cnf(c_6,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_746,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_125,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_15])).

cnf(c_126,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_125])).

cnf(c_20,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_126,c_20])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ v1_subset_1(X0,sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | v1_xboole_0(X0)
    | k6_domain_1(sK2,sK3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_262])).

cnf(c_283,plain,
    ( ~ m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
    | v1_xboole_0(k6_domain_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_735,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_284,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_890,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_891,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_911,plain,
    ( v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_24,c_25,c_284,c_891])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_745,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1295,plain,
    ( k6_domain_1(sK2,sK3) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_745])).

cnf(c_1771,plain,
    ( k6_domain_1(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_746,c_1295])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_738,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1288,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3)
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_738])).

cnf(c_893,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1576,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1288,c_23,c_22,c_893])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_742,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1579,plain,
    ( r2_hidden(sK3,k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_742])).

cnf(c_1912,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1771,c_1579])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2290,c_1912])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.91/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.91/1.03  
% 0.91/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.91/1.03  
% 0.91/1.03  ------  iProver source info
% 0.91/1.03  
% 0.91/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.91/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.91/1.03  git: non_committed_changes: false
% 0.91/1.03  git: last_make_outside_of_git: false
% 0.91/1.03  
% 0.91/1.03  ------ 
% 0.91/1.03  
% 0.91/1.03  ------ Input Options
% 0.91/1.03  
% 0.91/1.03  --out_options                           all
% 0.91/1.03  --tptp_safe_out                         true
% 0.91/1.03  --problem_path                          ""
% 0.91/1.03  --include_path                          ""
% 0.91/1.03  --clausifier                            res/vclausify_rel
% 0.91/1.03  --clausifier_options                    --mode clausify
% 0.91/1.03  --stdin                                 false
% 0.91/1.03  --stats_out                             all
% 0.91/1.03  
% 0.91/1.03  ------ General Options
% 0.91/1.03  
% 0.91/1.03  --fof                                   false
% 0.91/1.03  --time_out_real                         305.
% 0.91/1.03  --time_out_virtual                      -1.
% 0.91/1.03  --symbol_type_check                     false
% 0.91/1.03  --clausify_out                          false
% 0.91/1.03  --sig_cnt_out                           false
% 0.91/1.03  --trig_cnt_out                          false
% 0.91/1.03  --trig_cnt_out_tolerance                1.
% 0.91/1.03  --trig_cnt_out_sk_spl                   false
% 0.91/1.03  --abstr_cl_out                          false
% 0.91/1.03  
% 0.91/1.03  ------ Global Options
% 0.91/1.03  
% 0.91/1.03  --schedule                              default
% 0.91/1.03  --add_important_lit                     false
% 0.91/1.03  --prop_solver_per_cl                    1000
% 0.91/1.03  --min_unsat_core                        false
% 0.91/1.03  --soft_assumptions                      false
% 0.91/1.03  --soft_lemma_size                       3
% 0.91/1.03  --prop_impl_unit_size                   0
% 0.91/1.03  --prop_impl_unit                        []
% 0.91/1.03  --share_sel_clauses                     true
% 0.91/1.03  --reset_solvers                         false
% 0.91/1.03  --bc_imp_inh                            [conj_cone]
% 0.91/1.03  --conj_cone_tolerance                   3.
% 0.91/1.03  --extra_neg_conj                        none
% 0.91/1.03  --large_theory_mode                     true
% 0.91/1.03  --prolific_symb_bound                   200
% 0.91/1.03  --lt_threshold                          2000
% 0.91/1.03  --clause_weak_htbl                      true
% 0.91/1.03  --gc_record_bc_elim                     false
% 0.91/1.03  
% 0.91/1.03  ------ Preprocessing Options
% 0.91/1.03  
% 0.91/1.03  --preprocessing_flag                    true
% 0.91/1.03  --time_out_prep_mult                    0.1
% 0.91/1.03  --splitting_mode                        input
% 0.91/1.03  --splitting_grd                         true
% 0.91/1.03  --splitting_cvd                         false
% 0.91/1.03  --splitting_cvd_svl                     false
% 0.91/1.03  --splitting_nvd                         32
% 0.91/1.03  --sub_typing                            true
% 0.91/1.03  --prep_gs_sim                           true
% 0.91/1.03  --prep_unflatten                        true
% 0.91/1.03  --prep_res_sim                          true
% 0.91/1.03  --prep_upred                            true
% 0.91/1.03  --prep_sem_filter                       exhaustive
% 0.91/1.03  --prep_sem_filter_out                   false
% 0.91/1.03  --pred_elim                             true
% 0.91/1.03  --res_sim_input                         true
% 0.91/1.03  --eq_ax_congr_red                       true
% 0.91/1.03  --pure_diseq_elim                       true
% 0.91/1.03  --brand_transform                       false
% 0.91/1.03  --non_eq_to_eq                          false
% 0.91/1.03  --prep_def_merge                        true
% 0.91/1.03  --prep_def_merge_prop_impl              false
% 0.91/1.03  --prep_def_merge_mbd                    true
% 0.91/1.03  --prep_def_merge_tr_red                 false
% 0.91/1.03  --prep_def_merge_tr_cl                  false
% 0.91/1.03  --smt_preprocessing                     true
% 0.91/1.03  --smt_ac_axioms                         fast
% 0.91/1.03  --preprocessed_out                      false
% 0.91/1.03  --preprocessed_stats                    false
% 0.91/1.03  
% 0.91/1.03  ------ Abstraction refinement Options
% 0.91/1.03  
% 0.91/1.03  --abstr_ref                             []
% 0.91/1.03  --abstr_ref_prep                        false
% 0.91/1.03  --abstr_ref_until_sat                   false
% 0.91/1.03  --abstr_ref_sig_restrict                funpre
% 0.91/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.91/1.03  --abstr_ref_under                       []
% 0.91/1.03  
% 0.91/1.03  ------ SAT Options
% 0.91/1.03  
% 0.91/1.03  --sat_mode                              false
% 0.91/1.03  --sat_fm_restart_options                ""
% 0.91/1.03  --sat_gr_def                            false
% 0.91/1.03  --sat_epr_types                         true
% 0.91/1.03  --sat_non_cyclic_types                  false
% 0.91/1.03  --sat_finite_models                     false
% 0.91/1.03  --sat_fm_lemmas                         false
% 0.91/1.03  --sat_fm_prep                           false
% 0.91/1.03  --sat_fm_uc_incr                        true
% 0.91/1.03  --sat_out_model                         small
% 0.91/1.03  --sat_out_clauses                       false
% 0.91/1.03  
% 0.91/1.03  ------ QBF Options
% 0.91/1.03  
% 0.91/1.03  --qbf_mode                              false
% 0.91/1.03  --qbf_elim_univ                         false
% 0.91/1.03  --qbf_dom_inst                          none
% 0.91/1.03  --qbf_dom_pre_inst                      false
% 0.91/1.03  --qbf_sk_in                             false
% 0.91/1.03  --qbf_pred_elim                         true
% 0.91/1.03  --qbf_split                             512
% 0.91/1.03  
% 0.91/1.03  ------ BMC1 Options
% 0.91/1.03  
% 0.91/1.03  --bmc1_incremental                      false
% 0.91/1.03  --bmc1_axioms                           reachable_all
% 0.91/1.03  --bmc1_min_bound                        0
% 0.91/1.03  --bmc1_max_bound                        -1
% 0.91/1.03  --bmc1_max_bound_default                -1
% 0.91/1.03  --bmc1_symbol_reachability              true
% 0.91/1.03  --bmc1_property_lemmas                  false
% 0.91/1.03  --bmc1_k_induction                      false
% 0.91/1.03  --bmc1_non_equiv_states                 false
% 0.91/1.03  --bmc1_deadlock                         false
% 0.91/1.03  --bmc1_ucm                              false
% 0.91/1.03  --bmc1_add_unsat_core                   none
% 0.91/1.03  --bmc1_unsat_core_children              false
% 0.91/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.91/1.03  --bmc1_out_stat                         full
% 0.91/1.03  --bmc1_ground_init                      false
% 0.91/1.03  --bmc1_pre_inst_next_state              false
% 0.91/1.03  --bmc1_pre_inst_state                   false
% 0.91/1.03  --bmc1_pre_inst_reach_state             false
% 0.91/1.03  --bmc1_out_unsat_core                   false
% 0.91/1.03  --bmc1_aig_witness_out                  false
% 0.91/1.03  --bmc1_verbose                          false
% 0.91/1.03  --bmc1_dump_clauses_tptp                false
% 0.91/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.91/1.03  --bmc1_dump_file                        -
% 0.91/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.91/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.91/1.03  --bmc1_ucm_extend_mode                  1
% 0.91/1.03  --bmc1_ucm_init_mode                    2
% 0.91/1.03  --bmc1_ucm_cone_mode                    none
% 0.91/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.91/1.03  --bmc1_ucm_relax_model                  4
% 0.91/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.91/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.91/1.03  --bmc1_ucm_layered_model                none
% 0.91/1.03  --bmc1_ucm_max_lemma_size               10
% 0.91/1.03  
% 0.91/1.03  ------ AIG Options
% 0.91/1.03  
% 0.91/1.03  --aig_mode                              false
% 0.91/1.03  
% 0.91/1.03  ------ Instantiation Options
% 0.91/1.03  
% 0.91/1.03  --instantiation_flag                    true
% 0.91/1.03  --inst_sos_flag                         false
% 0.91/1.03  --inst_sos_phase                        true
% 0.91/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.91/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.91/1.03  --inst_lit_sel_side                     num_symb
% 0.91/1.03  --inst_solver_per_active                1400
% 0.91/1.03  --inst_solver_calls_frac                1.
% 0.91/1.03  --inst_passive_queue_type               priority_queues
% 0.91/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.91/1.03  --inst_passive_queues_freq              [25;2]
% 0.91/1.03  --inst_dismatching                      true
% 0.91/1.03  --inst_eager_unprocessed_to_passive     true
% 0.91/1.03  --inst_prop_sim_given                   true
% 0.91/1.03  --inst_prop_sim_new                     false
% 0.91/1.03  --inst_subs_new                         false
% 0.91/1.03  --inst_eq_res_simp                      false
% 0.91/1.03  --inst_subs_given                       false
% 0.91/1.03  --inst_orphan_elimination               true
% 0.91/1.03  --inst_learning_loop_flag               true
% 0.91/1.03  --inst_learning_start                   3000
% 0.91/1.03  --inst_learning_factor                  2
% 0.91/1.03  --inst_start_prop_sim_after_learn       3
% 0.91/1.03  --inst_sel_renew                        solver
% 0.91/1.03  --inst_lit_activity_flag                true
% 0.91/1.03  --inst_restr_to_given                   false
% 0.91/1.03  --inst_activity_threshold               500
% 0.91/1.03  --inst_out_proof                        true
% 0.91/1.03  
% 0.91/1.03  ------ Resolution Options
% 0.91/1.03  
% 0.91/1.03  --resolution_flag                       true
% 0.91/1.03  --res_lit_sel                           adaptive
% 0.91/1.03  --res_lit_sel_side                      none
% 0.91/1.03  --res_ordering                          kbo
% 0.91/1.03  --res_to_prop_solver                    active
% 0.91/1.03  --res_prop_simpl_new                    false
% 0.91/1.03  --res_prop_simpl_given                  true
% 0.91/1.03  --res_passive_queue_type                priority_queues
% 0.91/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.91/1.03  --res_passive_queues_freq               [15;5]
% 0.91/1.03  --res_forward_subs                      full
% 0.91/1.03  --res_backward_subs                     full
% 0.91/1.03  --res_forward_subs_resolution           true
% 0.91/1.03  --res_backward_subs_resolution          true
% 0.91/1.03  --res_orphan_elimination                true
% 0.91/1.03  --res_time_limit                        2.
% 0.91/1.03  --res_out_proof                         true
% 0.91/1.03  
% 0.91/1.03  ------ Superposition Options
% 0.91/1.03  
% 0.91/1.03  --superposition_flag                    true
% 0.91/1.03  --sup_passive_queue_type                priority_queues
% 0.91/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.91/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.91/1.03  --demod_completeness_check              fast
% 0.91/1.03  --demod_use_ground                      true
% 0.91/1.03  --sup_to_prop_solver                    passive
% 0.91/1.03  --sup_prop_simpl_new                    true
% 0.91/1.03  --sup_prop_simpl_given                  true
% 0.91/1.03  --sup_fun_splitting                     false
% 0.91/1.03  --sup_smt_interval                      50000
% 0.91/1.03  
% 0.91/1.03  ------ Superposition Simplification Setup
% 0.91/1.03  
% 0.91/1.03  --sup_indices_passive                   []
% 0.91/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.91/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.03  --sup_full_bw                           [BwDemod]
% 0.91/1.03  --sup_immed_triv                        [TrivRules]
% 0.91/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.91/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.03  --sup_immed_bw_main                     []
% 0.91/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.91/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/1.03  
% 0.91/1.03  ------ Combination Options
% 0.91/1.03  
% 0.91/1.03  --comb_res_mult                         3
% 0.91/1.03  --comb_sup_mult                         2
% 0.91/1.03  --comb_inst_mult                        10
% 0.91/1.03  
% 0.91/1.03  ------ Debug Options
% 0.91/1.03  
% 0.91/1.03  --dbg_backtrace                         false
% 0.91/1.03  --dbg_dump_prop_clauses                 false
% 0.91/1.03  --dbg_dump_prop_clauses_file            -
% 0.91/1.03  --dbg_out_stat                          false
% 0.91/1.03  ------ Parsing...
% 0.91/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.91/1.03  
% 0.91/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.91/1.03  
% 0.91/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.91/1.03  
% 0.91/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.91/1.03  ------ Proving...
% 0.91/1.03  ------ Problem Properties 
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  clauses                                 20
% 0.91/1.03  conjectures                             2
% 0.91/1.03  EPR                                     5
% 0.91/1.03  Horn                                    12
% 0.91/1.03  unary                                   6
% 0.91/1.03  binary                                  4
% 0.91/1.03  lits                                    45
% 0.91/1.03  lits eq                                 12
% 0.91/1.03  fd_pure                                 0
% 0.91/1.03  fd_pseudo                               0
% 0.91/1.03  fd_cond                                 0
% 0.91/1.03  fd_pseudo_cond                          6
% 0.91/1.03  AC symbols                              0
% 0.91/1.03  
% 0.91/1.03  ------ Schedule dynamic 5 is on 
% 0.91/1.03  
% 0.91/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  ------ 
% 0.91/1.03  Current options:
% 0.91/1.03  ------ 
% 0.91/1.03  
% 0.91/1.03  ------ Input Options
% 0.91/1.03  
% 0.91/1.03  --out_options                           all
% 0.91/1.03  --tptp_safe_out                         true
% 0.91/1.03  --problem_path                          ""
% 0.91/1.03  --include_path                          ""
% 0.91/1.03  --clausifier                            res/vclausify_rel
% 0.91/1.03  --clausifier_options                    --mode clausify
% 0.91/1.03  --stdin                                 false
% 0.91/1.03  --stats_out                             all
% 0.91/1.03  
% 0.91/1.03  ------ General Options
% 0.91/1.03  
% 0.91/1.03  --fof                                   false
% 0.91/1.03  --time_out_real                         305.
% 0.91/1.03  --time_out_virtual                      -1.
% 0.91/1.03  --symbol_type_check                     false
% 0.91/1.03  --clausify_out                          false
% 0.91/1.03  --sig_cnt_out                           false
% 0.91/1.03  --trig_cnt_out                          false
% 0.91/1.03  --trig_cnt_out_tolerance                1.
% 0.91/1.03  --trig_cnt_out_sk_spl                   false
% 0.91/1.03  --abstr_cl_out                          false
% 0.91/1.03  
% 0.91/1.03  ------ Global Options
% 0.91/1.03  
% 0.91/1.03  --schedule                              default
% 0.91/1.03  --add_important_lit                     false
% 0.91/1.03  --prop_solver_per_cl                    1000
% 0.91/1.03  --min_unsat_core                        false
% 0.91/1.03  --soft_assumptions                      false
% 0.91/1.03  --soft_lemma_size                       3
% 0.91/1.03  --prop_impl_unit_size                   0
% 0.91/1.03  --prop_impl_unit                        []
% 0.91/1.03  --share_sel_clauses                     true
% 0.91/1.03  --reset_solvers                         false
% 0.91/1.03  --bc_imp_inh                            [conj_cone]
% 0.91/1.03  --conj_cone_tolerance                   3.
% 0.91/1.03  --extra_neg_conj                        none
% 0.91/1.03  --large_theory_mode                     true
% 0.91/1.03  --prolific_symb_bound                   200
% 0.91/1.03  --lt_threshold                          2000
% 0.91/1.03  --clause_weak_htbl                      true
% 0.91/1.03  --gc_record_bc_elim                     false
% 0.91/1.03  
% 0.91/1.03  ------ Preprocessing Options
% 0.91/1.03  
% 0.91/1.03  --preprocessing_flag                    true
% 0.91/1.03  --time_out_prep_mult                    0.1
% 0.91/1.03  --splitting_mode                        input
% 0.91/1.03  --splitting_grd                         true
% 0.91/1.03  --splitting_cvd                         false
% 0.91/1.03  --splitting_cvd_svl                     false
% 0.91/1.03  --splitting_nvd                         32
% 0.91/1.03  --sub_typing                            true
% 0.91/1.03  --prep_gs_sim                           true
% 0.91/1.03  --prep_unflatten                        true
% 0.91/1.03  --prep_res_sim                          true
% 0.91/1.03  --prep_upred                            true
% 0.91/1.03  --prep_sem_filter                       exhaustive
% 0.91/1.03  --prep_sem_filter_out                   false
% 0.91/1.03  --pred_elim                             true
% 0.91/1.03  --res_sim_input                         true
% 0.91/1.03  --eq_ax_congr_red                       true
% 0.91/1.03  --pure_diseq_elim                       true
% 0.91/1.03  --brand_transform                       false
% 0.91/1.03  --non_eq_to_eq                          false
% 0.91/1.03  --prep_def_merge                        true
% 0.91/1.03  --prep_def_merge_prop_impl              false
% 0.91/1.03  --prep_def_merge_mbd                    true
% 0.91/1.03  --prep_def_merge_tr_red                 false
% 0.91/1.03  --prep_def_merge_tr_cl                  false
% 0.91/1.03  --smt_preprocessing                     true
% 0.91/1.03  --smt_ac_axioms                         fast
% 0.91/1.03  --preprocessed_out                      false
% 0.91/1.03  --preprocessed_stats                    false
% 0.91/1.03  
% 0.91/1.03  ------ Abstraction refinement Options
% 0.91/1.03  
% 0.91/1.03  --abstr_ref                             []
% 0.91/1.03  --abstr_ref_prep                        false
% 0.91/1.03  --abstr_ref_until_sat                   false
% 0.91/1.03  --abstr_ref_sig_restrict                funpre
% 0.91/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.91/1.03  --abstr_ref_under                       []
% 0.91/1.03  
% 0.91/1.03  ------ SAT Options
% 0.91/1.03  
% 0.91/1.03  --sat_mode                              false
% 0.91/1.03  --sat_fm_restart_options                ""
% 0.91/1.03  --sat_gr_def                            false
% 0.91/1.03  --sat_epr_types                         true
% 0.91/1.03  --sat_non_cyclic_types                  false
% 0.91/1.03  --sat_finite_models                     false
% 0.91/1.03  --sat_fm_lemmas                         false
% 0.91/1.03  --sat_fm_prep                           false
% 0.91/1.03  --sat_fm_uc_incr                        true
% 0.91/1.03  --sat_out_model                         small
% 0.91/1.03  --sat_out_clauses                       false
% 0.91/1.03  
% 0.91/1.03  ------ QBF Options
% 0.91/1.03  
% 0.91/1.03  --qbf_mode                              false
% 0.91/1.03  --qbf_elim_univ                         false
% 0.91/1.03  --qbf_dom_inst                          none
% 0.91/1.03  --qbf_dom_pre_inst                      false
% 0.91/1.03  --qbf_sk_in                             false
% 0.91/1.03  --qbf_pred_elim                         true
% 0.91/1.03  --qbf_split                             512
% 0.91/1.03  
% 0.91/1.03  ------ BMC1 Options
% 0.91/1.03  
% 0.91/1.03  --bmc1_incremental                      false
% 0.91/1.03  --bmc1_axioms                           reachable_all
% 0.91/1.03  --bmc1_min_bound                        0
% 0.91/1.03  --bmc1_max_bound                        -1
% 0.91/1.03  --bmc1_max_bound_default                -1
% 0.91/1.03  --bmc1_symbol_reachability              true
% 0.91/1.03  --bmc1_property_lemmas                  false
% 0.91/1.03  --bmc1_k_induction                      false
% 0.91/1.03  --bmc1_non_equiv_states                 false
% 0.91/1.03  --bmc1_deadlock                         false
% 0.91/1.03  --bmc1_ucm                              false
% 0.91/1.03  --bmc1_add_unsat_core                   none
% 0.91/1.03  --bmc1_unsat_core_children              false
% 0.91/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.91/1.03  --bmc1_out_stat                         full
% 0.91/1.03  --bmc1_ground_init                      false
% 0.91/1.03  --bmc1_pre_inst_next_state              false
% 0.91/1.03  --bmc1_pre_inst_state                   false
% 0.91/1.03  --bmc1_pre_inst_reach_state             false
% 0.91/1.03  --bmc1_out_unsat_core                   false
% 0.91/1.03  --bmc1_aig_witness_out                  false
% 0.91/1.03  --bmc1_verbose                          false
% 0.91/1.03  --bmc1_dump_clauses_tptp                false
% 0.91/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.91/1.03  --bmc1_dump_file                        -
% 0.91/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.91/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.91/1.03  --bmc1_ucm_extend_mode                  1
% 0.91/1.03  --bmc1_ucm_init_mode                    2
% 0.91/1.03  --bmc1_ucm_cone_mode                    none
% 0.91/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.91/1.03  --bmc1_ucm_relax_model                  4
% 0.91/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.91/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.91/1.03  --bmc1_ucm_layered_model                none
% 0.91/1.03  --bmc1_ucm_max_lemma_size               10
% 0.91/1.03  
% 0.91/1.03  ------ AIG Options
% 0.91/1.03  
% 0.91/1.03  --aig_mode                              false
% 0.91/1.03  
% 0.91/1.03  ------ Instantiation Options
% 0.91/1.03  
% 0.91/1.03  --instantiation_flag                    true
% 0.91/1.03  --inst_sos_flag                         false
% 0.91/1.03  --inst_sos_phase                        true
% 0.91/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.91/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.91/1.03  --inst_lit_sel_side                     none
% 0.91/1.03  --inst_solver_per_active                1400
% 0.91/1.03  --inst_solver_calls_frac                1.
% 0.91/1.03  --inst_passive_queue_type               priority_queues
% 0.91/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.91/1.03  --inst_passive_queues_freq              [25;2]
% 0.91/1.03  --inst_dismatching                      true
% 0.91/1.03  --inst_eager_unprocessed_to_passive     true
% 0.91/1.03  --inst_prop_sim_given                   true
% 0.91/1.03  --inst_prop_sim_new                     false
% 0.91/1.03  --inst_subs_new                         false
% 0.91/1.03  --inst_eq_res_simp                      false
% 0.91/1.03  --inst_subs_given                       false
% 0.91/1.03  --inst_orphan_elimination               true
% 0.91/1.03  --inst_learning_loop_flag               true
% 0.91/1.03  --inst_learning_start                   3000
% 0.91/1.03  --inst_learning_factor                  2
% 0.91/1.03  --inst_start_prop_sim_after_learn       3
% 0.91/1.03  --inst_sel_renew                        solver
% 0.91/1.03  --inst_lit_activity_flag                true
% 0.91/1.03  --inst_restr_to_given                   false
% 0.91/1.03  --inst_activity_threshold               500
% 0.91/1.03  --inst_out_proof                        true
% 0.91/1.03  
% 0.91/1.03  ------ Resolution Options
% 0.91/1.03  
% 0.91/1.03  --resolution_flag                       false
% 0.91/1.03  --res_lit_sel                           adaptive
% 0.91/1.03  --res_lit_sel_side                      none
% 0.91/1.03  --res_ordering                          kbo
% 0.91/1.03  --res_to_prop_solver                    active
% 0.91/1.03  --res_prop_simpl_new                    false
% 0.91/1.03  --res_prop_simpl_given                  true
% 0.91/1.03  --res_passive_queue_type                priority_queues
% 0.91/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.91/1.03  --res_passive_queues_freq               [15;5]
% 0.91/1.03  --res_forward_subs                      full
% 0.91/1.03  --res_backward_subs                     full
% 0.91/1.03  --res_forward_subs_resolution           true
% 0.91/1.03  --res_backward_subs_resolution          true
% 0.91/1.03  --res_orphan_elimination                true
% 0.91/1.03  --res_time_limit                        2.
% 0.91/1.03  --res_out_proof                         true
% 0.91/1.03  
% 0.91/1.03  ------ Superposition Options
% 0.91/1.03  
% 0.91/1.03  --superposition_flag                    true
% 0.91/1.03  --sup_passive_queue_type                priority_queues
% 0.91/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.91/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.91/1.03  --demod_completeness_check              fast
% 0.91/1.03  --demod_use_ground                      true
% 0.91/1.03  --sup_to_prop_solver                    passive
% 0.91/1.03  --sup_prop_simpl_new                    true
% 0.91/1.03  --sup_prop_simpl_given                  true
% 0.91/1.03  --sup_fun_splitting                     false
% 0.91/1.03  --sup_smt_interval                      50000
% 0.91/1.03  
% 0.91/1.03  ------ Superposition Simplification Setup
% 0.91/1.03  
% 0.91/1.03  --sup_indices_passive                   []
% 0.91/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.91/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.03  --sup_full_bw                           [BwDemod]
% 0.91/1.03  --sup_immed_triv                        [TrivRules]
% 0.91/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.91/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.03  --sup_immed_bw_main                     []
% 0.91/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.91/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/1.03  
% 0.91/1.03  ------ Combination Options
% 0.91/1.03  
% 0.91/1.03  --comb_res_mult                         3
% 0.91/1.03  --comb_sup_mult                         2
% 0.91/1.03  --comb_inst_mult                        10
% 0.91/1.03  
% 0.91/1.03  ------ Debug Options
% 0.91/1.03  
% 0.91/1.03  --dbg_backtrace                         false
% 0.91/1.03  --dbg_dump_prop_clauses                 false
% 0.91/1.03  --dbg_dump_prop_clauses_file            -
% 0.91/1.03  --dbg_out_stat                          false
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  ------ Proving...
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  % SZS status Theorem for theBenchmark.p
% 0.91/1.03  
% 0.91/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.91/1.03  
% 0.91/1.03  fof(f16,conjecture,(
% 0.91/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f17,negated_conjecture,(
% 0.91/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.91/1.03    inference(negated_conjecture,[],[f16])).
% 0.91/1.03  
% 0.91/1.03  fof(f29,plain,(
% 0.91/1.03    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.91/1.03    inference(ennf_transformation,[],[f17])).
% 0.91/1.03  
% 0.91/1.03  fof(f30,plain,(
% 0.91/1.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.91/1.03    inference(flattening,[],[f29])).
% 0.91/1.03  
% 0.91/1.03  fof(f41,plain,(
% 0.91/1.03    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK3),X0) & m1_subset_1(sK3,X0))) )),
% 0.91/1.03    introduced(choice_axiom,[])).
% 0.91/1.03  
% 0.91/1.03  fof(f40,plain,(
% 0.91/1.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) & ~v1_xboole_0(sK2))),
% 0.91/1.03    introduced(choice_axiom,[])).
% 0.91/1.03  
% 0.91/1.03  fof(f42,plain,(
% 0.91/1.03    (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2)) & ~v1_xboole_0(sK2)),
% 0.91/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f41,f40])).
% 0.91/1.03  
% 0.91/1.03  fof(f67,plain,(
% 0.91/1.03    m1_subset_1(sK3,sK2)),
% 0.91/1.03    inference(cnf_transformation,[],[f42])).
% 0.91/1.03  
% 0.91/1.03  fof(f12,axiom,(
% 0.91/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f21,plain,(
% 0.91/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.91/1.03    inference(ennf_transformation,[],[f12])).
% 0.91/1.03  
% 0.91/1.03  fof(f22,plain,(
% 0.91/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.91/1.03    inference(flattening,[],[f21])).
% 0.91/1.03  
% 0.91/1.03  fof(f62,plain,(
% 0.91/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f22])).
% 0.91/1.03  
% 0.91/1.03  fof(f66,plain,(
% 0.91/1.03    ~v1_xboole_0(sK2)),
% 0.91/1.03    inference(cnf_transformation,[],[f42])).
% 0.91/1.03  
% 0.91/1.03  fof(f4,axiom,(
% 0.91/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f18,plain,(
% 0.91/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.91/1.03    inference(ennf_transformation,[],[f4])).
% 0.91/1.03  
% 0.91/1.03  fof(f51,plain,(
% 0.91/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f18])).
% 0.91/1.03  
% 0.91/1.03  fof(f5,axiom,(
% 0.91/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f52,plain,(
% 0.91/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f5])).
% 0.91/1.03  
% 0.91/1.03  fof(f1,axiom,(
% 0.91/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f31,plain,(
% 0.91/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.91/1.03    inference(nnf_transformation,[],[f1])).
% 0.91/1.03  
% 0.91/1.03  fof(f32,plain,(
% 0.91/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.91/1.03    inference(flattening,[],[f31])).
% 0.91/1.03  
% 0.91/1.03  fof(f33,plain,(
% 0.91/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.91/1.03    inference(rectify,[],[f32])).
% 0.91/1.03  
% 0.91/1.03  fof(f34,plain,(
% 0.91/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.91/1.03    introduced(choice_axiom,[])).
% 0.91/1.03  
% 0.91/1.03  fof(f35,plain,(
% 0.91/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.91/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 0.91/1.03  
% 0.91/1.03  fof(f44,plain,(
% 0.91/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.91/1.03    inference(cnf_transformation,[],[f35])).
% 0.91/1.03  
% 0.91/1.03  fof(f3,axiom,(
% 0.91/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f50,plain,(
% 0.91/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.91/1.03    inference(cnf_transformation,[],[f3])).
% 0.91/1.03  
% 0.91/1.03  fof(f75,plain,(
% 0.91/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.91/1.03    inference(definition_unfolding,[],[f44,f50])).
% 0.91/1.03  
% 0.91/1.03  fof(f83,plain,(
% 0.91/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.91/1.03    inference(equality_resolution,[],[f75])).
% 0.91/1.03  
% 0.91/1.03  fof(f6,axiom,(
% 0.91/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f53,plain,(
% 0.91/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.91/1.03    inference(cnf_transformation,[],[f6])).
% 0.91/1.03  
% 0.91/1.03  fof(f2,axiom,(
% 0.91/1.03    v1_xboole_0(k1_xboole_0)),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f49,plain,(
% 0.91/1.03    v1_xboole_0(k1_xboole_0)),
% 0.91/1.03    inference(cnf_transformation,[],[f2])).
% 0.91/1.03  
% 0.91/1.03  fof(f68,plain,(
% 0.91/1.03    v1_subset_1(k6_domain_1(sK2,sK3),sK2)),
% 0.91/1.03    inference(cnf_transformation,[],[f42])).
% 0.91/1.03  
% 0.91/1.03  fof(f15,axiom,(
% 0.91/1.03    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f27,plain,(
% 0.91/1.03    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.91/1.03    inference(ennf_transformation,[],[f15])).
% 0.91/1.03  
% 0.91/1.03  fof(f28,plain,(
% 0.91/1.03    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.91/1.03    inference(flattening,[],[f27])).
% 0.91/1.03  
% 0.91/1.03  fof(f65,plain,(
% 0.91/1.03    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f28])).
% 0.91/1.03  
% 0.91/1.03  fof(f11,axiom,(
% 0.91/1.03    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f20,plain,(
% 0.91/1.03    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.91/1.03    inference(ennf_transformation,[],[f11])).
% 0.91/1.03  
% 0.91/1.03  fof(f61,plain,(
% 0.91/1.03    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f20])).
% 0.91/1.03  
% 0.91/1.03  fof(f69,plain,(
% 0.91/1.03    v1_zfmisc_1(sK2)),
% 0.91/1.03    inference(cnf_transformation,[],[f42])).
% 0.91/1.03  
% 0.91/1.03  fof(f13,axiom,(
% 0.91/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f23,plain,(
% 0.91/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.91/1.03    inference(ennf_transformation,[],[f13])).
% 0.91/1.03  
% 0.91/1.03  fof(f24,plain,(
% 0.91/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.91/1.03    inference(flattening,[],[f23])).
% 0.91/1.03  
% 0.91/1.03  fof(f63,plain,(
% 0.91/1.03    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f24])).
% 0.91/1.03  
% 0.91/1.03  fof(f7,axiom,(
% 0.91/1.03    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f19,plain,(
% 0.91/1.03    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.91/1.03    inference(ennf_transformation,[],[f7])).
% 0.91/1.03  
% 0.91/1.03  fof(f54,plain,(
% 0.91/1.03    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f19])).
% 0.91/1.03  
% 0.91/1.03  fof(f14,axiom,(
% 0.91/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f25,plain,(
% 0.91/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.91/1.03    inference(ennf_transformation,[],[f14])).
% 0.91/1.03  
% 0.91/1.03  fof(f26,plain,(
% 0.91/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.91/1.03    inference(flattening,[],[f25])).
% 0.91/1.03  
% 0.91/1.03  fof(f64,plain,(
% 0.91/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f26])).
% 0.91/1.03  
% 0.91/1.03  fof(f9,axiom,(
% 0.91/1.03    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f59,plain,(
% 0.91/1.03    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f9])).
% 0.91/1.03  
% 0.91/1.03  fof(f10,axiom,(
% 0.91/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f60,plain,(
% 0.91/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.91/1.03    inference(cnf_transformation,[],[f10])).
% 0.91/1.03  
% 0.91/1.03  fof(f70,plain,(
% 0.91/1.03    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.91/1.03    inference(definition_unfolding,[],[f59,f60])).
% 0.91/1.03  
% 0.91/1.03  fof(f81,plain,(
% 0.91/1.03    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.91/1.03    inference(definition_unfolding,[],[f64,f70])).
% 0.91/1.03  
% 0.91/1.03  fof(f8,axiom,(
% 0.91/1.03    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.91/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.03  
% 0.91/1.03  fof(f36,plain,(
% 0.91/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.91/1.03    inference(nnf_transformation,[],[f8])).
% 0.91/1.03  
% 0.91/1.03  fof(f37,plain,(
% 0.91/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.91/1.03    inference(rectify,[],[f36])).
% 0.91/1.03  
% 0.91/1.03  fof(f38,plain,(
% 0.91/1.03    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 0.91/1.03    introduced(choice_axiom,[])).
% 0.91/1.03  
% 0.91/1.03  fof(f39,plain,(
% 0.91/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.91/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 0.91/1.03  
% 0.91/1.03  fof(f56,plain,(
% 0.91/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.91/1.03    inference(cnf_transformation,[],[f39])).
% 0.91/1.03  
% 0.91/1.03  fof(f79,plain,(
% 0.91/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 0.91/1.03    inference(definition_unfolding,[],[f56,f70])).
% 0.91/1.03  
% 0.91/1.03  fof(f85,plain,(
% 0.91/1.03    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 0.91/1.03    inference(equality_resolution,[],[f79])).
% 0.91/1.03  
% 0.91/1.03  fof(f86,plain,(
% 0.91/1.03    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 0.91/1.03    inference(equality_resolution,[],[f85])).
% 0.91/1.03  
% 0.91/1.03  cnf(c_22,negated_conjecture,
% 0.91/1.03      ( m1_subset_1(sK3,sK2) ),
% 0.91/1.03      inference(cnf_transformation,[],[f67]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_737,plain,
% 0.91/1.03      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_16,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 0.91/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_740,plain,
% 0.91/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 0.91/1.03      | r2_hidden(X0,X1) = iProver_top
% 0.91/1.03      | v1_xboole_0(X1) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1386,plain,
% 0.91/1.03      ( r2_hidden(sK3,sK2) = iProver_top
% 0.91/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 0.91/1.03      inference(superposition,[status(thm)],[c_737,c_740]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_23,negated_conjecture,
% 0.91/1.03      ( ~ v1_xboole_0(sK2) ),
% 0.91/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_24,plain,
% 0.91/1.03      ( v1_xboole_0(sK2) != iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_25,plain,
% 0.91/1.03      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_887,plain,
% 0.91/1.03      ( ~ m1_subset_1(sK3,sK2) | r2_hidden(sK3,sK2) | v1_xboole_0(sK2) ),
% 0.91/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_888,plain,
% 0.91/1.03      ( m1_subset_1(sK3,sK2) != iProver_top
% 0.91/1.03      | r2_hidden(sK3,sK2) = iProver_top
% 0.91/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_887]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1547,plain,
% 0.91/1.03      ( r2_hidden(sK3,sK2) = iProver_top ),
% 0.91/1.03      inference(global_propositional_subsumption,
% 0.91/1.03                [status(thm)],
% 0.91/1.03                [c_1386,c_24,c_25,c_888]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_7,plain,
% 0.91/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 0.91/1.03      inference(cnf_transformation,[],[f51]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_8,plain,
% 0.91/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 0.91/1.03      inference(cnf_transformation,[],[f52]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_254,plain,
% 0.91/1.03      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 0.91/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_255,plain,
% 0.91/1.03      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.91/1.03      inference(unflattening,[status(thm)],[c_254]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_4,plain,
% 0.91/1.03      ( ~ r2_hidden(X0,X1)
% 0.91/1.03      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 0.91/1.03      inference(cnf_transformation,[],[f83]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_748,plain,
% 0.91/1.03      ( r2_hidden(X0,X1) != iProver_top
% 0.91/1.03      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1541,plain,
% 0.91/1.03      ( r2_hidden(X0,X1) != iProver_top
% 0.91/1.03      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 0.91/1.03      inference(superposition,[status(thm)],[c_255,c_748]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_9,plain,
% 0.91/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.91/1.03      inference(cnf_transformation,[],[f53]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1542,plain,
% 0.91/1.03      ( r2_hidden(X0,X1) != iProver_top
% 0.91/1.03      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.91/1.03      inference(demodulation,[status(thm)],[c_1541,c_9]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_2290,plain,
% 0.91/1.03      ( r2_hidden(sK3,k1_xboole_0) != iProver_top ),
% 0.91/1.03      inference(superposition,[status(thm)],[c_1547,c_1542]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_6,plain,
% 0.91/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 0.91/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_746,plain,
% 0.91/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_21,negated_conjecture,
% 0.91/1.03      ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
% 0.91/1.03      inference(cnf_transformation,[],[f68]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_19,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.91/1.03      | ~ v1_subset_1(X0,X1)
% 0.91/1.03      | ~ v1_zfmisc_1(X1)
% 0.91/1.03      | v1_xboole_0(X0)
% 0.91/1.03      | v1_xboole_0(X1) ),
% 0.91/1.03      inference(cnf_transformation,[],[f65]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_15,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.91/1.03      | ~ v1_subset_1(X0,X1)
% 0.91/1.03      | ~ v1_xboole_0(X1) ),
% 0.91/1.03      inference(cnf_transformation,[],[f61]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_125,plain,
% 0.91/1.03      ( v1_xboole_0(X0)
% 0.91/1.03      | ~ v1_zfmisc_1(X1)
% 0.91/1.03      | ~ v1_subset_1(X0,X1)
% 0.91/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.91/1.03      inference(global_propositional_subsumption,
% 0.91/1.03                [status(thm)],
% 0.91/1.03                [c_19,c_15]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_126,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.91/1.03      | ~ v1_subset_1(X0,X1)
% 0.91/1.03      | ~ v1_zfmisc_1(X1)
% 0.91/1.03      | v1_xboole_0(X0) ),
% 0.91/1.03      inference(renaming,[status(thm)],[c_125]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_20,negated_conjecture,
% 0.91/1.03      ( v1_zfmisc_1(sK2) ),
% 0.91/1.03      inference(cnf_transformation,[],[f69]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_261,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.91/1.03      | ~ v1_subset_1(X0,X1)
% 0.91/1.03      | v1_xboole_0(X0)
% 0.91/1.03      | sK2 != X1 ),
% 0.91/1.03      inference(resolution_lifted,[status(thm)],[c_126,c_20]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_262,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 0.91/1.03      | ~ v1_subset_1(X0,sK2)
% 0.91/1.03      | v1_xboole_0(X0) ),
% 0.91/1.03      inference(unflattening,[status(thm)],[c_261]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_282,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 0.91/1.03      | v1_xboole_0(X0)
% 0.91/1.03      | k6_domain_1(sK2,sK3) != X0
% 0.91/1.03      | sK2 != sK2 ),
% 0.91/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_262]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_283,plain,
% 0.91/1.03      ( ~ m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
% 0.91/1.03      | v1_xboole_0(k6_domain_1(sK2,sK3)) ),
% 0.91/1.03      inference(unflattening,[status(thm)],[c_282]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_735,plain,
% 0.91/1.03      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
% 0.91/1.03      | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_284,plain,
% 0.91/1.03      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
% 0.91/1.03      | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_17,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,X1)
% 0.91/1.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 0.91/1.03      | v1_xboole_0(X1) ),
% 0.91/1.03      inference(cnf_transformation,[],[f63]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_890,plain,
% 0.91/1.03      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
% 0.91/1.03      | ~ m1_subset_1(sK3,sK2)
% 0.91/1.03      | v1_xboole_0(sK2) ),
% 0.91/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_891,plain,
% 0.91/1.03      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top
% 0.91/1.03      | m1_subset_1(sK3,sK2) != iProver_top
% 0.91/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_911,plain,
% 0.91/1.03      ( v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 0.91/1.03      inference(global_propositional_subsumption,
% 0.91/1.03                [status(thm)],
% 0.91/1.03                [c_735,c_24,c_25,c_284,c_891]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_10,plain,
% 0.91/1.03      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 0.91/1.03      inference(cnf_transformation,[],[f54]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_745,plain,
% 0.91/1.03      ( X0 = X1
% 0.91/1.03      | v1_xboole_0(X0) != iProver_top
% 0.91/1.03      | v1_xboole_0(X1) != iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1295,plain,
% 0.91/1.03      ( k6_domain_1(sK2,sK3) = X0 | v1_xboole_0(X0) != iProver_top ),
% 0.91/1.03      inference(superposition,[status(thm)],[c_911,c_745]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1771,plain,
% 0.91/1.03      ( k6_domain_1(sK2,sK3) = k1_xboole_0 ),
% 0.91/1.03      inference(superposition,[status(thm)],[c_746,c_1295]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_18,plain,
% 0.91/1.03      ( ~ m1_subset_1(X0,X1)
% 0.91/1.03      | v1_xboole_0(X1)
% 0.91/1.03      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 0.91/1.03      inference(cnf_transformation,[],[f81]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_738,plain,
% 0.91/1.03      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 0.91/1.03      | m1_subset_1(X0,X1) != iProver_top
% 0.91/1.03      | v1_xboole_0(X1) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1288,plain,
% 0.91/1.03      ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3)
% 0.91/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 0.91/1.03      inference(superposition,[status(thm)],[c_737,c_738]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_893,plain,
% 0.91/1.03      ( ~ m1_subset_1(sK3,sK2)
% 0.91/1.03      | v1_xboole_0(sK2)
% 0.91/1.03      | k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
% 0.91/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1576,plain,
% 0.91/1.03      ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
% 0.91/1.03      inference(global_propositional_subsumption,
% 0.91/1.03                [status(thm)],
% 0.91/1.03                [c_1288,c_23,c_22,c_893]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_13,plain,
% 0.91/1.03      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 0.91/1.03      inference(cnf_transformation,[],[f86]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_742,plain,
% 0.91/1.03      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 0.91/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1579,plain,
% 0.91/1.03      ( r2_hidden(sK3,k6_domain_1(sK2,sK3)) = iProver_top ),
% 0.91/1.03      inference(superposition,[status(thm)],[c_1576,c_742]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(c_1912,plain,
% 0.91/1.03      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 0.91/1.03      inference(demodulation,[status(thm)],[c_1771,c_1579]) ).
% 0.91/1.03  
% 0.91/1.03  cnf(contradiction,plain,
% 0.91/1.03      ( $false ),
% 0.91/1.03      inference(minisat,[status(thm)],[c_2290,c_1912]) ).
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.91/1.03  
% 0.91/1.03  ------                               Statistics
% 0.91/1.03  
% 0.91/1.03  ------ General
% 0.91/1.03  
% 0.91/1.03  abstr_ref_over_cycles:                  0
% 0.91/1.03  abstr_ref_under_cycles:                 0
% 0.91/1.03  gc_basic_clause_elim:                   0
% 0.91/1.03  forced_gc_time:                         0
% 0.91/1.03  parsing_time:                           0.018
% 0.91/1.03  unif_index_cands_time:                  0.
% 0.91/1.03  unif_index_add_time:                    0.
% 0.91/1.03  orderings_time:                         0.
% 0.91/1.03  out_proof_time:                         0.007
% 0.91/1.03  total_time:                             0.12
% 0.91/1.03  num_of_symbols:                         47
% 0.91/1.03  num_of_terms:                           2290
% 0.91/1.03  
% 0.91/1.03  ------ Preprocessing
% 0.91/1.03  
% 0.91/1.03  num_of_splits:                          0
% 0.91/1.03  num_of_split_atoms:                     0
% 0.91/1.03  num_of_reused_defs:                     0
% 0.91/1.03  num_eq_ax_congr_red:                    33
% 0.91/1.03  num_of_sem_filtered_clauses:            1
% 0.91/1.03  num_of_subtypes:                        0
% 0.91/1.03  monotx_restored_types:                  0
% 0.91/1.03  sat_num_of_epr_types:                   0
% 0.91/1.03  sat_num_of_non_cyclic_types:            0
% 0.91/1.03  sat_guarded_non_collapsed_types:        0
% 0.91/1.03  num_pure_diseq_elim:                    0
% 0.91/1.03  simp_replaced_by:                       0
% 0.91/1.03  res_preprocessed:                       103
% 0.91/1.03  prep_upred:                             0
% 0.91/1.03  prep_unflattend:                        6
% 0.91/1.03  smt_new_axioms:                         0
% 0.91/1.03  pred_elim_cands:                        3
% 0.91/1.03  pred_elim:                              3
% 0.91/1.03  pred_elim_cl:                           4
% 0.91/1.03  pred_elim_cycles:                       5
% 0.91/1.03  merged_defs:                            0
% 0.91/1.03  merged_defs_ncl:                        0
% 0.91/1.03  bin_hyper_res:                          0
% 0.91/1.03  prep_cycles:                            4
% 0.91/1.03  pred_elim_time:                         0.002
% 0.91/1.03  splitting_time:                         0.
% 0.91/1.03  sem_filter_time:                        0.
% 0.91/1.03  monotx_time:                            0.001
% 0.91/1.03  subtype_inf_time:                       0.
% 0.91/1.03  
% 0.91/1.03  ------ Problem properties
% 0.91/1.03  
% 0.91/1.03  clauses:                                20
% 0.91/1.03  conjectures:                            2
% 0.91/1.03  epr:                                    5
% 0.91/1.03  horn:                                   12
% 0.91/1.03  ground:                                 4
% 0.91/1.03  unary:                                  6
% 0.91/1.03  binary:                                 4
% 0.91/1.03  lits:                                   45
% 0.91/1.03  lits_eq:                                12
% 0.91/1.03  fd_pure:                                0
% 0.91/1.03  fd_pseudo:                              0
% 0.91/1.03  fd_cond:                                0
% 0.91/1.03  fd_pseudo_cond:                         6
% 0.91/1.03  ac_symbols:                             0
% 0.91/1.03  
% 0.91/1.03  ------ Propositional Solver
% 0.91/1.03  
% 0.91/1.03  prop_solver_calls:                      25
% 0.91/1.03  prop_fast_solver_calls:                 533
% 0.91/1.03  smt_solver_calls:                       0
% 0.91/1.03  smt_fast_solver_calls:                  0
% 0.91/1.03  prop_num_of_clauses:                    883
% 0.91/1.03  prop_preprocess_simplified:             3905
% 0.91/1.03  prop_fo_subsumed:                       4
% 0.91/1.03  prop_solver_time:                       0.
% 0.91/1.03  smt_solver_time:                        0.
% 0.91/1.03  smt_fast_solver_time:                   0.
% 0.91/1.03  prop_fast_solver_time:                  0.
% 0.91/1.03  prop_unsat_core_time:                   0.
% 0.91/1.03  
% 0.91/1.03  ------ QBF
% 0.91/1.03  
% 0.91/1.03  qbf_q_res:                              0
% 0.91/1.03  qbf_num_tautologies:                    0
% 0.91/1.03  qbf_prep_cycles:                        0
% 0.91/1.03  
% 0.91/1.03  ------ BMC1
% 0.91/1.03  
% 0.91/1.03  bmc1_current_bound:                     -1
% 0.91/1.03  bmc1_last_solved_bound:                 -1
% 0.91/1.03  bmc1_unsat_core_size:                   -1
% 0.91/1.03  bmc1_unsat_core_parents_size:           -1
% 0.91/1.03  bmc1_merge_next_fun:                    0
% 0.91/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.91/1.03  
% 0.91/1.03  ------ Instantiation
% 0.91/1.03  
% 0.91/1.03  inst_num_of_clauses:                    280
% 0.91/1.03  inst_num_in_passive:                    41
% 0.91/1.03  inst_num_in_active:                     105
% 0.91/1.03  inst_num_in_unprocessed:                134
% 0.91/1.03  inst_num_of_loops:                      120
% 0.91/1.03  inst_num_of_learning_restarts:          0
% 0.91/1.03  inst_num_moves_active_passive:          14
% 0.91/1.03  inst_lit_activity:                      0
% 0.91/1.03  inst_lit_activity_moves:                0
% 0.91/1.03  inst_num_tautologies:                   0
% 0.91/1.03  inst_num_prop_implied:                  0
% 0.91/1.03  inst_num_existing_simplified:           0
% 0.91/1.03  inst_num_eq_res_simplified:             0
% 0.91/1.03  inst_num_child_elim:                    0
% 0.91/1.03  inst_num_of_dismatching_blockings:      19
% 0.91/1.03  inst_num_of_non_proper_insts:           137
% 0.91/1.03  inst_num_of_duplicates:                 0
% 0.91/1.03  inst_inst_num_from_inst_to_res:         0
% 0.91/1.03  inst_dismatching_checking_time:         0.
% 0.91/1.03  
% 0.91/1.03  ------ Resolution
% 0.91/1.03  
% 0.91/1.03  res_num_of_clauses:                     0
% 0.91/1.03  res_num_in_passive:                     0
% 0.91/1.03  res_num_in_active:                      0
% 0.91/1.03  res_num_of_loops:                       107
% 0.91/1.03  res_forward_subset_subsumed:            14
% 0.91/1.03  res_backward_subset_subsumed:           0
% 0.91/1.03  res_forward_subsumed:                   0
% 0.91/1.03  res_backward_subsumed:                  0
% 0.91/1.03  res_forward_subsumption_resolution:     0
% 0.91/1.03  res_backward_subsumption_resolution:    0
% 0.91/1.03  res_clause_to_clause_subsumption:       66
% 0.91/1.03  res_orphan_elimination:                 0
% 0.91/1.03  res_tautology_del:                      10
% 0.91/1.03  res_num_eq_res_simplified:              0
% 0.91/1.03  res_num_sel_changes:                    0
% 0.91/1.03  res_moves_from_active_to_pass:          0
% 0.91/1.03  
% 0.91/1.03  ------ Superposition
% 0.91/1.03  
% 0.91/1.03  sup_time_total:                         0.
% 0.91/1.03  sup_time_generating:                    0.
% 0.91/1.03  sup_time_sim_full:                      0.
% 0.91/1.03  sup_time_sim_immed:                     0.
% 0.91/1.03  
% 0.91/1.03  sup_num_of_clauses:                     31
% 0.91/1.03  sup_num_in_active:                      18
% 0.91/1.03  sup_num_in_passive:                     13
% 0.91/1.03  sup_num_of_loops:                       23
% 0.91/1.03  sup_fw_superposition:                   14
% 0.91/1.03  sup_bw_superposition:                   9
% 0.91/1.03  sup_immediate_simplified:               2
% 0.91/1.03  sup_given_eliminated:                   2
% 0.91/1.03  comparisons_done:                       0
% 0.91/1.03  comparisons_avoided:                    2
% 0.91/1.03  
% 0.91/1.03  ------ Simplifications
% 0.91/1.03  
% 0.91/1.03  
% 0.91/1.03  sim_fw_subset_subsumed:                 0
% 0.91/1.03  sim_bw_subset_subsumed:                 0
% 0.91/1.03  sim_fw_subsumed:                        0
% 0.91/1.03  sim_bw_subsumed:                        2
% 0.91/1.03  sim_fw_subsumption_res:                 0
% 0.91/1.03  sim_bw_subsumption_res:                 0
% 0.91/1.03  sim_tautology_del:                      1
% 0.91/1.03  sim_eq_tautology_del:                   3
% 0.91/1.03  sim_eq_res_simp:                        0
% 0.91/1.03  sim_fw_demodulated:                     2
% 0.91/1.03  sim_bw_demodulated:                     5
% 0.91/1.03  sim_light_normalised:                   0
% 0.91/1.03  sim_joinable_taut:                      0
% 0.91/1.03  sim_joinable_simp:                      0
% 0.91/1.03  sim_ac_normalised:                      0
% 0.91/1.03  sim_smt_subsumption:                    0
% 0.91/1.03  
%------------------------------------------------------------------------------
