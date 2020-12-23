%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:56 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 323 expanded)
%              Number of clauses        :   93 ( 123 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  422 ( 941 expanded)
%              Number of equality atoms :  158 ( 225 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

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

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f71,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK2(X0),X0)
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f42])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

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

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f65,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_382,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1466,plain,
    ( X0 != X1
    | k6_domain_1(sK3,sK4) != X1
    | k6_domain_1(sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_1903,plain,
    ( X0 != k6_domain_1(sK3,sK4)
    | k6_domain_1(sK3,sK4) = X0
    | k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_15338,plain,
    ( k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4)
    | k6_domain_1(sK3,sK4) = k1_xboole_0
    | k1_xboole_0 != k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_1619,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_4710,plain,
    ( k3_xboole_0(k6_domain_1(sK3,sK4),X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k3_xboole_0(k6_domain_1(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_8935,plain,
    ( k3_xboole_0(k6_domain_1(sK3,sK4),X0) != k3_xboole_0(X1,k6_domain_1(sK3,sK4))
    | k1_xboole_0 != k3_xboole_0(X1,k6_domain_1(sK3,sK4))
    | k1_xboole_0 = k3_xboole_0(k6_domain_1(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_4710])).

cnf(c_8936,plain,
    ( k3_xboole_0(k6_domain_1(sK3,sK4),sK3) != k3_xboole_0(sK3,k6_domain_1(sK3,sK4))
    | k1_xboole_0 = k3_xboole_0(k6_domain_1(sK3,sK4),sK3)
    | k1_xboole_0 != k3_xboole_0(sK3,k6_domain_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8935])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8530,plain,
    ( k3_xboole_0(k6_domain_1(sK3,sK4),X0) = k3_xboole_0(X0,k6_domain_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8535,plain,
    ( k3_xboole_0(k6_domain_1(sK3,sK4),sK3) = k3_xboole_0(sK3,k6_domain_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8530])).

cnf(c_1171,plain,
    ( X0 != X1
    | X0 = k6_domain_1(sK3,sK4)
    | k6_domain_1(sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_2793,plain,
    ( k6_domain_1(sK3,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_6771,plain,
    ( k6_domain_1(sK3,sK4) != k3_xboole_0(k6_domain_1(sK3,sK4),X0)
    | k1_xboole_0 = k6_domain_1(sK3,sK4)
    | k1_xboole_0 != k3_xboole_0(k6_domain_1(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2793])).

cnf(c_6772,plain,
    ( k6_domain_1(sK3,sK4) != k3_xboole_0(k6_domain_1(sK3,sK4),sK3)
    | k1_xboole_0 = k6_domain_1(sK3,sK4)
    | k1_xboole_0 != k3_xboole_0(k6_domain_1(sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_6771])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3646,plain,
    ( ~ v1_xboole_0(k3_xboole_0(X0,k6_domain_1(sK3,sK4)))
    | k1_xboole_0 = k3_xboole_0(X0,k6_domain_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3648,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK3,k6_domain_1(sK3,sK4)))
    | k1_xboole_0 = k3_xboole_0(sK3,k6_domain_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3646])).

cnf(c_3400,plain,
    ( k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4)
    | k6_domain_1(sK3,sK4) = k3_xboole_0(k6_domain_1(sK3,sK4),X0)
    | k3_xboole_0(k6_domain_1(sK3,sK4),X0) != k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_3401,plain,
    ( k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4)
    | k6_domain_1(sK3,sK4) = k3_xboole_0(k6_domain_1(sK3,sK4),sK3)
    | k3_xboole_0(k6_domain_1(sK3,sK4),sK3) != k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3400])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_859,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_863,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2807,plain,
    ( k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_863])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1060,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3)
    | k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3216,plain,
    ( k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2807,c_24,c_23,c_1060])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1378,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_12])).

cnf(c_3219,plain,
    ( k6_domain_1(sK3,sK4) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3216,c_1378])).

cnf(c_386,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2322,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(sK2(X2),X2)
    | X2 != X1
    | sK2(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_2324,plain,
    ( v1_subset_1(sK2(sK3),sK3)
    | ~ v1_subset_1(sK3,sK3)
    | sK2(sK3) != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_15,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_867,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_865,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1745,plain,
    ( r1_tarski(sK2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_867,c_865])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_871,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2252,plain,
    ( sK2(X0) = X0
    | r1_tarski(X0,sK2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_871])).

cnf(c_2258,plain,
    ( sK2(sK3) = sK3
    | r1_tarski(sK3,sK2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_869,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1749,plain,
    ( k3_xboole_0(sK2(X0),X0) = sK2(X0) ),
    inference(superposition,[status(thm)],[c_1745,c_869])).

cnf(c_1844,plain,
    ( k3_xboole_0(X0,sK2(X0)) = sK2(X0) ),
    inference(superposition,[status(thm)],[c_0,c_1749])).

cnf(c_20,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_862,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1661,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_1669,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(k3_xboole_0(X0,X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1661,c_20])).

cnf(c_1671,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_1980,plain,
    ( v1_zfmisc_1(X0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_862,c_1671])).

cnf(c_1981,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1980])).

cnf(c_1991,plain,
    ( r1_tarski(X0,sK2(X0)) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(sK2(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_1981])).

cnf(c_2013,plain,
    ( r1_tarski(sK3,sK2(sK3)) = iProver_top
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(sK2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_1787,plain,
    ( r1_tarski(X0,k6_domain_1(sK3,sK4))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(X0,k6_domain_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1794,plain,
    ( r1_tarski(sK3,k6_domain_1(sK3,sK4))
    | ~ v1_zfmisc_1(sK3)
    | v1_xboole_0(k3_xboole_0(sK3,k6_domain_1(sK3,sK4)))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_147,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_183,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_148])).

cnf(c_857,plain,
    ( v1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_1750,plain,
    ( v1_subset_1(sK2(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_857])).

cnf(c_1761,plain,
    ( v1_subset_1(sK2(sK3),sK3) = iProver_top
    | v1_xboole_0(sK2(sK3)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_1328,plain,
    ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(X0))
    | r1_tarski(k6_domain_1(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
    | r1_tarski(k6_domain_1(sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_381,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1168,plain,
    ( k6_domain_1(sK3,sK4) = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1158,plain,
    ( ~ r1_tarski(k6_domain_1(sK3,sK4),X0)
    | k3_xboole_0(k6_domain_1(sK3,sK4),X0) = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1164,plain,
    ( ~ r1_tarski(k6_domain_1(sK3,sK4),sK3)
    | k3_xboole_0(k6_domain_1(sK3,sK4),sK3) = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_1146,plain,
    ( ~ r1_tarski(X0,k6_domain_1(sK3,sK4))
    | ~ r1_tarski(k6_domain_1(sK3,sK4),X0)
    | X0 = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1148,plain,
    ( ~ r1_tarski(k6_domain_1(sK3,sK4),sK3)
    | ~ r1_tarski(sK3,k6_domain_1(sK3,sK4))
    | sK3 = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_1063,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    | X0 != k6_domain_1(sK3,sK4)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_1065,plain,
    ( ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    | v1_subset_1(sK3,sK3)
    | sK3 != k6_domain_1(sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1051,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_61,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_57,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_47,plain,
    ( v1_subset_1(sK2(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_49,plain,
    ( v1_subset_1(sK2(sK3),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_48,plain,
    ( ~ v1_subset_1(sK2(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_21,negated_conjecture,
    ( v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,plain,
    ( v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15338,c_8936,c_8535,c_6772,c_3648,c_3401,c_3219,c_2324,c_2258,c_2013,c_1794,c_1761,c_1330,c_1168,c_1164,c_1148,c_1065,c_1051,c_61,c_57,c_49,c_48,c_28,c_21,c_22,c_23,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.78/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.99  
% 3.78/0.99  ------  iProver source info
% 3.78/0.99  
% 3.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.99  git: non_committed_changes: false
% 3.78/0.99  git: last_make_outside_of_git: false
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  ------ Parsing...
% 3.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.99  ------ Proving...
% 3.78/0.99  ------ Problem Properties 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  clauses                                 24
% 3.78/0.99  conjectures                             4
% 3.78/0.99  EPR                                     9
% 3.78/0.99  Horn                                    18
% 3.78/0.99  unary                                   10
% 3.78/0.99  binary                                  8
% 3.78/0.99  lits                                    46
% 3.78/0.99  lits eq                                 7
% 3.78/0.99  fd_pure                                 0
% 3.78/0.99  fd_pseudo                               0
% 3.78/0.99  fd_cond                                 1
% 3.78/0.99  fd_pseudo_cond                          1
% 3.78/0.99  AC symbols                              0
% 3.78/0.99  
% 3.78/0.99  ------ Input Options Time Limit: Unbounded
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  Current options:
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ Proving...
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS status Theorem for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  fof(f1,axiom,(
% 3.78/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f48,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f1])).
% 3.78/0.99  
% 3.78/0.99  fof(f4,axiom,(
% 3.78/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f20,plain,(
% 3.78/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f4])).
% 3.78/0.99  
% 3.78/0.99  fof(f54,plain,(
% 3.78/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f20])).
% 3.78/0.99  
% 3.78/0.99  fof(f17,conjecture,(
% 3.78/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f18,negated_conjecture,(
% 3.78/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 3.78/0.99    inference(negated_conjecture,[],[f17])).
% 3.78/0.99  
% 3.78/0.99  fof(f30,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f18])).
% 3.78/0.99  
% 3.78/0.99  fof(f31,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 3.78/0.99    inference(flattening,[],[f30])).
% 3.78/0.99  
% 3.78/0.99  fof(f46,plain,(
% 3.78/0.99    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK4),X0) & m1_subset_1(sK4,X0))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f45,plain,(
% 3.78/0.99    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,X1),sK3) & m1_subset_1(X1,sK3)) & ~v1_xboole_0(sK3))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f47,plain,(
% 3.78/0.99    (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,sK4),sK3) & m1_subset_1(sK4,sK3)) & ~v1_xboole_0(sK3)),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f46,f45])).
% 3.78/0.99  
% 3.78/0.99  fof(f72,plain,(
% 3.78/0.99    m1_subset_1(sK4,sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f47])).
% 3.78/0.99  
% 3.78/0.99  fof(f15,axiom,(
% 3.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f26,plain,(
% 3.78/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f15])).
% 3.78/0.99  
% 3.78/0.99  fof(f27,plain,(
% 3.78/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.78/0.99    inference(flattening,[],[f26])).
% 3.78/0.99  
% 3.78/0.99  fof(f69,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f27])).
% 3.78/0.99  
% 3.78/0.99  fof(f8,axiom,(
% 3.78/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f60,plain,(
% 3.78/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f8])).
% 3.78/0.99  
% 3.78/0.99  fof(f9,axiom,(
% 3.78/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f61,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f9])).
% 3.78/0.99  
% 3.78/0.99  fof(f75,plain,(
% 3.78/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.78/0.99    inference(definition_unfolding,[],[f60,f61])).
% 3.78/0.99  
% 3.78/0.99  fof(f77,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.78/0.99    inference(definition_unfolding,[],[f69,f75])).
% 3.78/0.99  
% 3.78/0.99  fof(f71,plain,(
% 3.78/0.99    ~v1_xboole_0(sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f47])).
% 3.78/0.99  
% 3.78/0.99  fof(f6,axiom,(
% 3.78/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f58,plain,(
% 3.78/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.78/0.99    inference(cnf_transformation,[],[f6])).
% 3.78/0.99  
% 3.78/0.99  fof(f10,axiom,(
% 3.78/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f62,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f10])).
% 3.78/0.99  
% 3.78/0.99  fof(f76,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 3.78/0.99    inference(definition_unfolding,[],[f62,f75])).
% 3.78/0.99  
% 3.78/0.99  fof(f12,axiom,(
% 3.78/0.99    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f42,plain,(
% 3.78/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f43,plain,(
% 3.78/0.99    ! [X0] : (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f64,plain,(
% 3.78/0.99    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f43])).
% 3.78/0.99  
% 3.78/0.99  fof(f13,axiom,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f44,plain,(
% 3.78/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.78/0.99    inference(nnf_transformation,[],[f13])).
% 3.78/0.99  
% 3.78/0.99  fof(f66,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f44])).
% 3.78/0.99  
% 3.78/0.99  fof(f5,axiom,(
% 3.78/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f40,plain,(
% 3.78/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.99    inference(nnf_transformation,[],[f5])).
% 3.78/0.99  
% 3.78/0.99  fof(f41,plain,(
% 3.78/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.99    inference(flattening,[],[f40])).
% 3.78/0.99  
% 3.78/0.99  fof(f57,plain,(
% 3.78/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f41])).
% 3.78/0.99  
% 3.78/0.99  fof(f7,axiom,(
% 3.78/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f21,plain,(
% 3.78/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f7])).
% 3.78/0.99  
% 3.78/0.99  fof(f59,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f21])).
% 3.78/0.99  
% 3.78/0.99  fof(f16,axiom,(
% 3.78/0.99    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f28,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f16])).
% 3.78/0.99  
% 3.78/0.99  fof(f29,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.78/0.99    inference(flattening,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f70,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f29])).
% 3.78/0.99  
% 3.78/0.99  fof(f2,axiom,(
% 3.78/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f32,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(nnf_transformation,[],[f2])).
% 3.78/0.99  
% 3.78/0.99  fof(f33,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(rectify,[],[f32])).
% 3.78/0.99  
% 3.78/0.99  fof(f34,plain,(
% 3.78/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f35,plain,(
% 3.78/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.78/0.99  
% 3.78/0.99  fof(f49,plain,(
% 3.78/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f35])).
% 3.78/0.99  
% 3.78/0.99  fof(f3,axiom,(
% 3.78/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f19,plain,(
% 3.78/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f3])).
% 3.78/0.99  
% 3.78/0.99  fof(f36,plain,(
% 3.78/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/0.99    inference(nnf_transformation,[],[f19])).
% 3.78/0.99  
% 3.78/0.99  fof(f37,plain,(
% 3.78/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/0.99    inference(rectify,[],[f36])).
% 3.78/0.99  
% 3.78/0.99  fof(f38,plain,(
% 3.78/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f39,plain,(
% 3.78/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.78/0.99  
% 3.78/0.99  fof(f52,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f11,axiom,(
% 3.78/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f22,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f11])).
% 3.78/0.99  
% 3.78/0.99  fof(f23,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.78/0.99    inference(flattening,[],[f22])).
% 3.78/0.99  
% 3.78/0.99  fof(f63,plain,(
% 3.78/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f23])).
% 3.78/0.99  
% 3.78/0.99  fof(f67,plain,(
% 3.78/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f44])).
% 3.78/0.99  
% 3.78/0.99  fof(f14,axiom,(
% 3.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f24,plain,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f14])).
% 3.78/0.99  
% 3.78/0.99  fof(f25,plain,(
% 3.78/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.78/0.99    inference(flattening,[],[f24])).
% 3.78/0.99  
% 3.78/0.99  fof(f68,plain,(
% 3.78/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f25])).
% 3.78/0.99  
% 3.78/0.99  fof(f55,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.78/0.99    inference(cnf_transformation,[],[f41])).
% 3.78/0.99  
% 3.78/0.99  fof(f79,plain,(
% 3.78/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.78/0.99    inference(equality_resolution,[],[f55])).
% 3.78/0.99  
% 3.78/0.99  fof(f65,plain,(
% 3.78/0.99    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f43])).
% 3.78/0.99  
% 3.78/0.99  fof(f74,plain,(
% 3.78/0.99    v1_zfmisc_1(sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f47])).
% 3.78/0.99  
% 3.78/0.99  fof(f73,plain,(
% 3.78/0.99    v1_subset_1(k6_domain_1(sK3,sK4),sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f47])).
% 3.78/0.99  
% 3.78/0.99  cnf(c_382,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1466,plain,
% 3.78/0.99      ( X0 != X1
% 3.78/0.99      | k6_domain_1(sK3,sK4) != X1
% 3.78/0.99      | k6_domain_1(sK3,sK4) = X0 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_382]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1903,plain,
% 3.78/0.99      ( X0 != k6_domain_1(sK3,sK4)
% 3.78/0.99      | k6_domain_1(sK3,sK4) = X0
% 3.78/0.99      | k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1466]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15338,plain,
% 3.78/0.99      ( k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4)
% 3.78/0.99      | k6_domain_1(sK3,sK4) = k1_xboole_0
% 3.78/0.99      | k1_xboole_0 != k6_domain_1(sK3,sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1903]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1619,plain,
% 3.78/0.99      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_382]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4710,plain,
% 3.78/0.99      ( k3_xboole_0(k6_domain_1(sK3,sK4),X0) != X1
% 3.78/0.99      | k1_xboole_0 != X1
% 3.78/0.99      | k1_xboole_0 = k3_xboole_0(k6_domain_1(sK3,sK4),X0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1619]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8935,plain,
% 3.78/0.99      ( k3_xboole_0(k6_domain_1(sK3,sK4),X0) != k3_xboole_0(X1,k6_domain_1(sK3,sK4))
% 3.78/0.99      | k1_xboole_0 != k3_xboole_0(X1,k6_domain_1(sK3,sK4))
% 3.78/0.99      | k1_xboole_0 = k3_xboole_0(k6_domain_1(sK3,sK4),X0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_4710]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8936,plain,
% 3.78/0.99      ( k3_xboole_0(k6_domain_1(sK3,sK4),sK3) != k3_xboole_0(sK3,k6_domain_1(sK3,sK4))
% 3.78/0.99      | k1_xboole_0 = k3_xboole_0(k6_domain_1(sK3,sK4),sK3)
% 3.78/0.99      | k1_xboole_0 != k3_xboole_0(sK3,k6_domain_1(sK3,sK4)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_8935]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_0,plain,
% 3.78/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8530,plain,
% 3.78/0.99      ( k3_xboole_0(k6_domain_1(sK3,sK4),X0) = k3_xboole_0(X0,k6_domain_1(sK3,sK4)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8535,plain,
% 3.78/0.99      ( k3_xboole_0(k6_domain_1(sK3,sK4),sK3) = k3_xboole_0(sK3,k6_domain_1(sK3,sK4)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_8530]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1171,plain,
% 3.78/0.99      ( X0 != X1
% 3.78/0.99      | X0 = k6_domain_1(sK3,sK4)
% 3.78/0.99      | k6_domain_1(sK3,sK4) != X1 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_382]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2793,plain,
% 3.78/0.99      ( k6_domain_1(sK3,sK4) != X0
% 3.78/0.99      | k1_xboole_0 != X0
% 3.78/0.99      | k1_xboole_0 = k6_domain_1(sK3,sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1171]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6771,plain,
% 3.78/0.99      ( k6_domain_1(sK3,sK4) != k3_xboole_0(k6_domain_1(sK3,sK4),X0)
% 3.78/0.99      | k1_xboole_0 = k6_domain_1(sK3,sK4)
% 3.78/0.99      | k1_xboole_0 != k3_xboole_0(k6_domain_1(sK3,sK4),X0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2793]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6772,plain,
% 3.78/0.99      ( k6_domain_1(sK3,sK4) != k3_xboole_0(k6_domain_1(sK3,sK4),sK3)
% 3.78/0.99      | k1_xboole_0 = k6_domain_1(sK3,sK4)
% 3.78/0.99      | k1_xboole_0 != k3_xboole_0(k6_domain_1(sK3,sK4),sK3) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_6771]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_6,plain,
% 3.78/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3646,plain,
% 3.78/0.99      ( ~ v1_xboole_0(k3_xboole_0(X0,k6_domain_1(sK3,sK4)))
% 3.78/0.99      | k1_xboole_0 = k3_xboole_0(X0,k6_domain_1(sK3,sK4)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3648,plain,
% 3.78/0.99      ( ~ v1_xboole_0(k3_xboole_0(sK3,k6_domain_1(sK3,sK4)))
% 3.78/0.99      | k1_xboole_0 = k3_xboole_0(sK3,k6_domain_1(sK3,sK4)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3646]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3400,plain,
% 3.78/0.99      ( k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4)
% 3.78/0.99      | k6_domain_1(sK3,sK4) = k3_xboole_0(k6_domain_1(sK3,sK4),X0)
% 3.78/0.99      | k3_xboole_0(k6_domain_1(sK3,sK4),X0) != k6_domain_1(sK3,sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1903]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3401,plain,
% 3.78/0.99      ( k6_domain_1(sK3,sK4) != k6_domain_1(sK3,sK4)
% 3.78/0.99      | k6_domain_1(sK3,sK4) = k3_xboole_0(k6_domain_1(sK3,sK4),sK3)
% 3.78/0.99      | k3_xboole_0(k6_domain_1(sK3,sK4),sK3) != k6_domain_1(sK3,sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3400]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_23,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK4,sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_859,plain,
% 3.78/0.99      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_19,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,X1)
% 3.78/0.99      | v1_xboole_0(X1)
% 3.78/0.99      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_863,plain,
% 3.78/0.99      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 3.78/0.99      | m1_subset_1(X0,X1) != iProver_top
% 3.78/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2807,plain,
% 3.78/0.99      ( k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4)
% 3.78/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_859,c_863]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_24,negated_conjecture,
% 3.78/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1060,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK4,sK3)
% 3.78/0.99      | v1_xboole_0(sK3)
% 3.78/0.99      | k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3216,plain,
% 3.78/0.99      ( k1_enumset1(sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_2807,c_24,c_23,c_1060]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_10,plain,
% 3.78/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12,plain,
% 3.78/0.99      ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) != k1_xboole_0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1378,plain,
% 3.78/0.99      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_10,c_12]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3219,plain,
% 3.78/0.99      ( k6_domain_1(sK3,sK4) != k1_xboole_0 ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_3216,c_1378]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_386,plain,
% 3.78/0.99      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2322,plain,
% 3.78/0.99      ( ~ v1_subset_1(X0,X1)
% 3.78/0.99      | v1_subset_1(sK2(X2),X2)
% 3.78/0.99      | X2 != X1
% 3.78/0.99      | sK2(X2) != X0 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_386]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2324,plain,
% 3.78/0.99      ( v1_subset_1(sK2(sK3),sK3)
% 3.78/0.99      | ~ v1_subset_1(sK3,sK3)
% 3.78/0.99      | sK2(sK3) != sK3
% 3.78/0.99      | sK3 != sK3 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2322]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15,plain,
% 3.78/0.99      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_867,plain,
% 3.78/0.99      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_17,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_865,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.78/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1745,plain,
% 3.78/0.99      ( r1_tarski(sK2(X0),X0) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_867,c_865]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_871,plain,
% 3.78/0.99      ( X0 = X1
% 3.78/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.78/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2252,plain,
% 3.78/0.99      ( sK2(X0) = X0 | r1_tarski(X0,sK2(X0)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1745,c_871]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2258,plain,
% 3.78/0.99      ( sK2(sK3) = sK3 | r1_tarski(sK3,sK2(sK3)) != iProver_top ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2252]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_869,plain,
% 3.78/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1749,plain,
% 3.78/0.99      ( k3_xboole_0(sK2(X0),X0) = sK2(X0) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1745,c_869]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1844,plain,
% 3.78/0.99      ( k3_xboole_0(X0,sK2(X0)) = sK2(X0) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_0,c_1749]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_20,plain,
% 3.78/0.99      ( r1_tarski(X0,X1)
% 3.78/0.99      | ~ v1_zfmisc_1(X0)
% 3.78/0.99      | v1_xboole_0(X0)
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(X0,X1)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_862,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.78/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.78/0.99      | v1_xboole_0(X0) = iProver_top
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2,plain,
% 3.78/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1661,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) | ~ v1_xboole_0(X0) ),
% 3.78/0.99      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1669,plain,
% 3.78/0.99      ( r1_tarski(X0,X1)
% 3.78/0.99      | ~ v1_zfmisc_1(X0)
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(X0,X1)) ),
% 3.78/0.99      inference(backward_subsumption_resolution,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1661,c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1671,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.78/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1980,plain,
% 3.78/0.99      ( v1_zfmisc_1(X0) != iProver_top
% 3.78/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_862,c_1671]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1981,plain,
% 3.78/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.78/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_1980]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1991,plain,
% 3.78/0.99      ( r1_tarski(X0,sK2(X0)) = iProver_top
% 3.78/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.78/0.99      | v1_xboole_0(sK2(X0)) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1844,c_1981]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2013,plain,
% 3.78/0.99      ( r1_tarski(sK3,sK2(sK3)) = iProver_top
% 3.78/0.99      | v1_zfmisc_1(sK3) != iProver_top
% 3.78/0.99      | v1_xboole_0(sK2(sK3)) = iProver_top ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1991]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1787,plain,
% 3.78/0.99      ( r1_tarski(X0,k6_domain_1(sK3,sK4))
% 3.78/0.99      | ~ v1_zfmisc_1(X0)
% 3.78/0.99      | v1_xboole_0(X0)
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(X0,k6_domain_1(sK3,sK4))) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1794,plain,
% 3.78/0.99      ( r1_tarski(sK3,k6_domain_1(sK3,sK4))
% 3.78/0.99      | ~ v1_zfmisc_1(sK3)
% 3.78/0.99      | v1_xboole_0(k3_xboole_0(sK3,k6_domain_1(sK3,sK4)))
% 3.78/0.99      | v1_xboole_0(sK3) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1787]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/0.99      | v1_subset_1(X0,X1)
% 3.78/0.99      | ~ v1_xboole_0(X0)
% 3.78/0.99      | v1_xboole_0(X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_16,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_147,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.78/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_148,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_147]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_183,plain,
% 3.78/0.99      ( v1_subset_1(X0,X1)
% 3.78/0.99      | ~ r1_tarski(X0,X1)
% 3.78/0.99      | ~ v1_xboole_0(X0)
% 3.78/0.99      | v1_xboole_0(X1) ),
% 3.78/0.99      inference(bin_hyper_res,[status(thm)],[c_13,c_148]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_857,plain,
% 3.78/0.99      ( v1_subset_1(X0,X1) = iProver_top
% 3.78/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.78/0.99      | v1_xboole_0(X0) != iProver_top
% 3.78/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1750,plain,
% 3.78/0.99      ( v1_subset_1(sK2(X0),X0) = iProver_top
% 3.78/0.99      | v1_xboole_0(X0) = iProver_top
% 3.78/0.99      | v1_xboole_0(sK2(X0)) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1745,c_857]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1761,plain,
% 3.78/0.99      ( v1_subset_1(sK2(sK3),sK3) = iProver_top
% 3.78/0.99      | v1_xboole_0(sK2(sK3)) != iProver_top
% 3.78/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1750]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1328,plain,
% 3.78/1.00      ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(X0))
% 3.78/1.00      | r1_tarski(k6_domain_1(sK3,sK4),X0) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1330,plain,
% 3.78/1.00      ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
% 3.78/1.00      | r1_tarski(k6_domain_1(sK3,sK4),sK3) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_1328]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_381,plain,( X0 = X0 ),theory(equality) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1168,plain,
% 3.78/1.00      ( k6_domain_1(sK3,sK4) = k6_domain_1(sK3,sK4) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_381]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1158,plain,
% 3.78/1.00      ( ~ r1_tarski(k6_domain_1(sK3,sK4),X0)
% 3.78/1.00      | k3_xboole_0(k6_domain_1(sK3,sK4),X0) = k6_domain_1(sK3,sK4) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1164,plain,
% 3.78/1.00      ( ~ r1_tarski(k6_domain_1(sK3,sK4),sK3)
% 3.78/1.00      | k3_xboole_0(k6_domain_1(sK3,sK4),sK3) = k6_domain_1(sK3,sK4) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_1158]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1146,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,k6_domain_1(sK3,sK4))
% 3.78/1.00      | ~ r1_tarski(k6_domain_1(sK3,sK4),X0)
% 3.78/1.00      | X0 = k6_domain_1(sK3,sK4) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1148,plain,
% 3.78/1.00      ( ~ r1_tarski(k6_domain_1(sK3,sK4),sK3)
% 3.78/1.00      | ~ r1_tarski(sK3,k6_domain_1(sK3,sK4))
% 3.78/1.00      | sK3 = k6_domain_1(sK3,sK4) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_1146]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1063,plain,
% 3.78/1.00      ( v1_subset_1(X0,X1)
% 3.78/1.00      | ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
% 3.78/1.00      | X0 != k6_domain_1(sK3,sK4)
% 3.78/1.00      | X1 != sK3 ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_386]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1065,plain,
% 3.78/1.00      ( ~ v1_subset_1(k6_domain_1(sK3,sK4),sK3)
% 3.78/1.00      | v1_subset_1(sK3,sK3)
% 3.78/1.00      | sK3 != k6_domain_1(sK3,sK4)
% 3.78/1.00      | sK3 != sK3 ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_1063]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_18,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,X1)
% 3.78/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.78/1.00      | v1_xboole_0(X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1051,plain,
% 3.78/1.00      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
% 3.78/1.00      | ~ m1_subset_1(sK4,sK3)
% 3.78/1.00      | v1_xboole_0(sK3) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_61,plain,
% 3.78/1.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_9,plain,
% 3.78/1.00      ( r1_tarski(X0,X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_57,plain,
% 3.78/1.00      ( r1_tarski(sK3,sK3) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_14,plain,
% 3.78/1.00      ( ~ v1_subset_1(sK2(X0),X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_47,plain,
% 3.78/1.00      ( v1_subset_1(sK2(X0),X0) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_49,plain,
% 3.78/1.00      ( v1_subset_1(sK2(sK3),sK3) != iProver_top ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_47]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_48,plain,
% 3.78/1.00      ( ~ v1_subset_1(sK2(sK3),sK3) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_21,negated_conjecture,
% 3.78/1.00      ( v1_zfmisc_1(sK3) ),
% 3.78/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_28,plain,
% 3.78/1.00      ( v1_zfmisc_1(sK3) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_22,negated_conjecture,
% 3.78/1.00      ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
% 3.78/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_25,plain,
% 3.78/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(contradiction,plain,
% 3.78/1.00      ( $false ),
% 3.78/1.00      inference(minisat,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_15338,c_8936,c_8535,c_6772,c_3648,c_3401,c_3219,
% 3.78/1.00                 c_2324,c_2258,c_2013,c_1794,c_1761,c_1330,c_1168,c_1164,
% 3.78/1.00                 c_1148,c_1065,c_1051,c_61,c_57,c_49,c_48,c_28,c_21,c_22,
% 3.78/1.00                 c_23,c_25,c_24]) ).
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  ------                               Statistics
% 3.78/1.00  
% 3.78/1.00  ------ Selected
% 3.78/1.00  
% 3.78/1.00  total_time:                             0.426
% 3.78/1.00  
%------------------------------------------------------------------------------
