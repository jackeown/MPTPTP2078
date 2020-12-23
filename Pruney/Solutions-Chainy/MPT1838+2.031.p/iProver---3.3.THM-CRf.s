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
% DateTime   : Thu Dec  3 12:24:36 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 614 expanded)
%              Number of clauses        :   81 ( 169 expanded)
%              Number of leaves         :   25 ( 157 expanded)
%              Depth                    :   19
%              Number of atoms          :  420 (2392 expanded)
%              Number of equality atoms :  193 ( 773 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK5 != X0
        & r1_tarski(X0,sK5)
        & v1_zfmisc_1(sK5)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r1_tarski(sK4,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( sK4 != sK5
    & r1_tarski(sK4,sK5)
    & v1_zfmisc_1(sK5)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f42,f41])).

fof(f75,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f77,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f80,f80])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) != k3_tarski(k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f78,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),X1)) ),
    inference(definition_unfolding,[],[f69,f80])).

fof(f74,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f55])).

fof(f93,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f92])).

cnf(c_722,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2045,plain,
    ( X0 != X1
    | X0 = sK0(sK4)
    | sK0(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_6952,plain,
    ( X0 = sK0(sK4)
    | X0 != sK4
    | sK0(sK4) != sK4 ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_6954,plain,
    ( sK0(sK4) != sK4
    | k1_xboole_0 = sK0(sK4)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_6952])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4668,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4414,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_345,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_30])).

cnf(c_346,plain,
    ( r2_hidden(sK0(sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1087,plain,
    ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,plain,
    ( m1_subset_1(sK3(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_296,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | sK3(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_297,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_29,negated_conjecture,
    ( v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_315,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_29])).

cnf(c_316,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_318,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_30])).

cnf(c_25,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_323,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_324,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_326,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_30])).

cnf(c_1114,plain,
    ( k1_tarski(sK3(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_318,c_326])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1090,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1961,plain,
    ( sK3(sK5) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1090])).

cnf(c_2117,plain,
    ( sK3(sK5) = sK0(sK5) ),
    inference(superposition,[status(thm)],[c_1087,c_1961])).

cnf(c_2133,plain,
    ( k1_tarski(sK0(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_2117,c_1114])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1089,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1096,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2281,plain,
    ( k4_xboole_0(sK4,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1089,c_1096])).

cnf(c_9,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2878,plain,
    ( k3_tarski(k2_enumset1(sK5,sK5,sK5,sK4)) = k3_tarski(k2_enumset1(sK5,sK5,sK5,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2281,c_9])).

cnf(c_7,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2880,plain,
    ( k3_tarski(k2_enumset1(sK5,sK5,sK5,sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_2878,c_7])).

cnf(c_14,plain,
    ( k1_tarski(X0) = X1
    | k3_tarski(k2_enumset1(X2,X2,X2,X1)) != k1_tarski(X0)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2945,plain,
    ( k1_tarski(X0) != sK5
    | k1_tarski(X0) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2880,c_14])).

cnf(c_3115,plain,
    ( k1_tarski(sK0(sK5)) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2133,c_2945])).

cnf(c_3116,plain,
    ( sK5 = sK4
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3115,c_2133])).

cnf(c_27,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3214,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3116,c_27])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1531,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(sK4),X0)
    | r2_hidden(sK0(sK4),X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3070,plain,
    ( ~ r1_tarski(X0,k1_tarski(sK4))
    | ~ r2_hidden(sK0(sK4),X0)
    | r2_hidden(sK0(sK4),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_3072,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK4))
    | r2_hidden(sK0(sK4),k1_tarski(sK4))
    | ~ r2_hidden(sK0(sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3070])).

cnf(c_1475,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK4))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2076,plain,
    ( ~ r2_hidden(sK0(sK4),k1_tarski(sK4))
    | sK0(sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_1847,plain,
    ( ~ r1_tarski(X0,k1_tarski(sK5))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1849,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK5))
    | r2_hidden(k1_xboole_0,k1_tarski(sK5))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_22,plain,
    ( k3_tarski(k2_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1649,plain,
    ( k3_tarski(k2_enumset1(sK5,sK5,sK5,X0)) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1114,c_22])).

cnf(c_1827,plain,
    ( sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_1649])).

cnf(c_1276,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1502,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_1503,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_1493,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1494,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1493])).

cnf(c_721,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1356,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1343,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK5))
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1345,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(sK5))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_725,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1315,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1317,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_724,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1254,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK4),sK4)
    | X0 != sK0(sK4)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1256,plain,
    ( ~ r2_hidden(sK0(sK4),sK4)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0(sK4)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1229,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK0(sK4),X0)
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1231,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r2_hidden(sK0(sK4),sK4)
    | r2_hidden(sK0(sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_352,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_31])).

cnf(c_353,plain,
    ( r2_hidden(sK0(sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_65,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_55,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_52,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6954,c_4668,c_4414,c_3214,c_3072,c_2076,c_1849,c_1827,c_1503,c_1494,c_1356,c_1345,c_1317,c_1256,c_1231,c_353,c_65,c_55,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:59:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.23/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.99  
% 3.23/0.99  ------  iProver source info
% 3.23/0.99  
% 3.23/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.99  git: non_committed_changes: false
% 3.23/0.99  git: last_make_outside_of_git: false
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options
% 3.23/0.99  
% 3.23/0.99  --out_options                           all
% 3.23/0.99  --tptp_safe_out                         true
% 3.23/0.99  --problem_path                          ""
% 3.23/0.99  --include_path                          ""
% 3.23/0.99  --clausifier                            res/vclausify_rel
% 3.23/0.99  --clausifier_options                    --mode clausify
% 3.23/0.99  --stdin                                 false
% 3.23/0.99  --stats_out                             all
% 3.23/0.99  
% 3.23/0.99  ------ General Options
% 3.23/0.99  
% 3.23/0.99  --fof                                   false
% 3.23/0.99  --time_out_real                         305.
% 3.23/0.99  --time_out_virtual                      -1.
% 3.23/0.99  --symbol_type_check                     false
% 3.23/0.99  --clausify_out                          false
% 3.23/0.99  --sig_cnt_out                           false
% 3.23/0.99  --trig_cnt_out                          false
% 3.23/0.99  --trig_cnt_out_tolerance                1.
% 3.23/0.99  --trig_cnt_out_sk_spl                   false
% 3.23/0.99  --abstr_cl_out                          false
% 3.23/0.99  
% 3.23/0.99  ------ Global Options
% 3.23/0.99  
% 3.23/0.99  --schedule                              default
% 3.23/0.99  --add_important_lit                     false
% 3.23/0.99  --prop_solver_per_cl                    1000
% 3.23/0.99  --min_unsat_core                        false
% 3.23/0.99  --soft_assumptions                      false
% 3.23/0.99  --soft_lemma_size                       3
% 3.23/0.99  --prop_impl_unit_size                   0
% 3.23/0.99  --prop_impl_unit                        []
% 3.23/0.99  --share_sel_clauses                     true
% 3.23/0.99  --reset_solvers                         false
% 3.23/0.99  --bc_imp_inh                            [conj_cone]
% 3.23/0.99  --conj_cone_tolerance                   3.
% 3.23/0.99  --extra_neg_conj                        none
% 3.23/0.99  --large_theory_mode                     true
% 3.23/0.99  --prolific_symb_bound                   200
% 3.23/0.99  --lt_threshold                          2000
% 3.23/0.99  --clause_weak_htbl                      true
% 3.23/0.99  --gc_record_bc_elim                     false
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing Options
% 3.23/0.99  
% 3.23/0.99  --preprocessing_flag                    true
% 3.23/0.99  --time_out_prep_mult                    0.1
% 3.23/0.99  --splitting_mode                        input
% 3.23/0.99  --splitting_grd                         true
% 3.23/0.99  --splitting_cvd                         false
% 3.23/0.99  --splitting_cvd_svl                     false
% 3.23/0.99  --splitting_nvd                         32
% 3.23/0.99  --sub_typing                            true
% 3.23/0.99  --prep_gs_sim                           true
% 3.23/0.99  --prep_unflatten                        true
% 3.23/0.99  --prep_res_sim                          true
% 3.23/0.99  --prep_upred                            true
% 3.23/0.99  --prep_sem_filter                       exhaustive
% 3.23/0.99  --prep_sem_filter_out                   false
% 3.23/0.99  --pred_elim                             true
% 3.23/0.99  --res_sim_input                         true
% 3.23/0.99  --eq_ax_congr_red                       true
% 3.23/0.99  --pure_diseq_elim                       true
% 3.23/0.99  --brand_transform                       false
% 3.23/0.99  --non_eq_to_eq                          false
% 3.23/0.99  --prep_def_merge                        true
% 3.23/0.99  --prep_def_merge_prop_impl              false
% 3.23/0.99  --prep_def_merge_mbd                    true
% 3.23/0.99  --prep_def_merge_tr_red                 false
% 3.23/0.99  --prep_def_merge_tr_cl                  false
% 3.23/0.99  --smt_preprocessing                     true
% 3.23/0.99  --smt_ac_axioms                         fast
% 3.23/0.99  --preprocessed_out                      false
% 3.23/0.99  --preprocessed_stats                    false
% 3.23/0.99  
% 3.23/0.99  ------ Abstraction refinement Options
% 3.23/0.99  
% 3.23/0.99  --abstr_ref                             []
% 3.23/0.99  --abstr_ref_prep                        false
% 3.23/0.99  --abstr_ref_until_sat                   false
% 3.23/0.99  --abstr_ref_sig_restrict                funpre
% 3.23/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.99  --abstr_ref_under                       []
% 3.23/0.99  
% 3.23/0.99  ------ SAT Options
% 3.23/0.99  
% 3.23/0.99  --sat_mode                              false
% 3.23/0.99  --sat_fm_restart_options                ""
% 3.23/0.99  --sat_gr_def                            false
% 3.23/0.99  --sat_epr_types                         true
% 3.23/0.99  --sat_non_cyclic_types                  false
% 3.23/0.99  --sat_finite_models                     false
% 3.23/0.99  --sat_fm_lemmas                         false
% 3.23/0.99  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     num_symb
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       true
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  ------ Parsing...
% 3.23/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.00  ------ Proving...
% 3.23/1.00  ------ Problem Properties 
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  clauses                                 24
% 3.23/1.00  conjectures                             2
% 3.23/1.00  EPR                                     4
% 3.23/1.00  Horn                                    18
% 3.23/1.00  unary                                   11
% 3.23/1.00  binary                                  6
% 3.23/1.00  lits                                    44
% 3.23/1.00  lits eq                                 25
% 3.23/1.00  fd_pure                                 0
% 3.23/1.00  fd_pseudo                               0
% 3.23/1.00  fd_cond                                 0
% 3.23/1.00  fd_pseudo_cond                          6
% 3.23/1.00  AC symbols                              0
% 3.23/1.00  
% 3.23/1.00  ------ Schedule dynamic 5 is on 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  Current options:
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     none
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       false
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ Proving...
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS status Theorem for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  fof(f5,axiom,(
% 3.23/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f52,plain,(
% 3.23/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f5])).
% 3.23/1.00  
% 3.23/1.00  fof(f1,axiom,(
% 3.23/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f24,plain,(
% 3.23/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.23/1.00    inference(nnf_transformation,[],[f1])).
% 3.23/1.00  
% 3.23/1.00  fof(f25,plain,(
% 3.23/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.23/1.00    inference(rectify,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f26,plain,(
% 3.23/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f27,plain,(
% 3.23/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.23/1.00  
% 3.23/1.00  fof(f45,plain,(
% 3.23/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f15,conjecture,(
% 3.23/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f16,negated_conjecture,(
% 3.23/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.23/1.00    inference(negated_conjecture,[],[f15])).
% 3.23/1.00  
% 3.23/1.00  fof(f22,plain,(
% 3.23/1.00    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f16])).
% 3.23/1.00  
% 3.23/1.00  fof(f23,plain,(
% 3.23/1.00    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.23/1.00    inference(flattening,[],[f22])).
% 3.23/1.00  
% 3.23/1.00  fof(f42,plain,(
% 3.23/1.00    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK5 != X0 & r1_tarski(X0,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f41,plain,(
% 3.23/1.00    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK4 != X1 & r1_tarski(sK4,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f43,plain,(
% 3.23/1.00    (sK4 != sK5 & r1_tarski(sK4,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f42,f41])).
% 3.23/1.00  
% 3.23/1.00  fof(f75,plain,(
% 3.23/1.00    ~v1_xboole_0(sK5)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f13,axiom,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f19,plain,(
% 3.23/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f13])).
% 3.23/1.00  
% 3.23/1.00  fof(f20,plain,(
% 3.23/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.23/1.00    inference(flattening,[],[f19])).
% 3.23/1.00  
% 3.23/1.00  fof(f70,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f20])).
% 3.23/1.00  
% 3.23/1.00  fof(f14,axiom,(
% 3.23/1.00    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f21,plain,(
% 3.23/1.00    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f14])).
% 3.23/1.00  
% 3.23/1.00  fof(f37,plain,(
% 3.23/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.23/1.00    inference(nnf_transformation,[],[f21])).
% 3.23/1.00  
% 3.23/1.00  fof(f38,plain,(
% 3.23/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.23/1.00    inference(rectify,[],[f37])).
% 3.23/1.00  
% 3.23/1.00  fof(f39,plain,(
% 3.23/1.00    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f40,plain,(
% 3.23/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 3.23/1.00  
% 3.23/1.00  fof(f71,plain,(
% 3.23/1.00    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f76,plain,(
% 3.23/1.00    v1_zfmisc_1(sK5)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f72,plain,(
% 3.23/1.00    ( ! [X0] : (k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f7,axiom,(
% 3.23/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f33,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.23/1.00    inference(nnf_transformation,[],[f7])).
% 3.23/1.00  
% 3.23/1.00  fof(f34,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.23/1.00    inference(rectify,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f35,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f36,plain,(
% 3.23/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 3.23/1.00  
% 3.23/1.00  fof(f54,plain,(
% 3.23/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.23/1.00    inference(cnf_transformation,[],[f36])).
% 3.23/1.00  
% 3.23/1.00  fof(f94,plain,(
% 3.23/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.23/1.00    inference(equality_resolution,[],[f54])).
% 3.23/1.00  
% 3.23/1.00  fof(f77,plain,(
% 3.23/1.00    r1_tarski(sK4,sK5)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f3,axiom,(
% 3.23/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f32,plain,(
% 3.23/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.23/1.00    inference(nnf_transformation,[],[f3])).
% 3.23/1.00  
% 3.23/1.00  fof(f50,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f32])).
% 3.23/1.00  
% 3.23/1.00  fof(f6,axiom,(
% 3.23/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f53,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f6])).
% 3.23/1.00  
% 3.23/1.00  fof(f10,axiom,(
% 3.23/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f60,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f10])).
% 3.23/1.00  
% 3.23/1.00  fof(f8,axiom,(
% 3.23/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f58,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f8])).
% 3.23/1.00  
% 3.23/1.00  fof(f9,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f59,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f9])).
% 3.23/1.00  
% 3.23/1.00  fof(f79,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.23/1.00    inference(definition_unfolding,[],[f58,f59])).
% 3.23/1.00  
% 3.23/1.00  fof(f80,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.23/1.00    inference(definition_unfolding,[],[f60,f79])).
% 3.23/1.00  
% 3.23/1.00  fof(f82,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 3.23/1.00    inference(definition_unfolding,[],[f53,f80,f80])).
% 3.23/1.00  
% 3.23/1.00  fof(f4,axiom,(
% 3.23/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f51,plain,(
% 3.23/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.23/1.00    inference(cnf_transformation,[],[f4])).
% 3.23/1.00  
% 3.23/1.00  fof(f81,plain,(
% 3.23/1.00    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.23/1.00    inference(definition_unfolding,[],[f51,f80])).
% 3.23/1.00  
% 3.23/1.00  fof(f11,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f18,plain,(
% 3.23/1.00    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f11])).
% 3.23/1.00  
% 3.23/1.00  fof(f68,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  fof(f83,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) != k3_tarski(k2_enumset1(X1,X1,X1,X2))) )),
% 3.23/1.00    inference(definition_unfolding,[],[f68,f80])).
% 3.23/1.00  
% 3.23/1.00  fof(f78,plain,(
% 3.23/1.00    sK4 != sK5),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f2,axiom,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f17,plain,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f2])).
% 3.23/1.00  
% 3.23/1.00  fof(f28,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(nnf_transformation,[],[f17])).
% 3.23/1.00  
% 3.23/1.00  fof(f29,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(rectify,[],[f28])).
% 3.23/1.00  
% 3.23/1.00  fof(f30,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f31,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.23/1.00  
% 3.23/1.00  fof(f46,plain,(
% 3.23/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f31])).
% 3.23/1.00  
% 3.23/1.00  fof(f12,axiom,(
% 3.23/1.00    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f69,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f12])).
% 3.23/1.00  
% 3.23/1.00  fof(f91,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),X1))) )),
% 3.23/1.00    inference(definition_unfolding,[],[f69,f80])).
% 3.23/1.00  
% 3.23/1.00  fof(f74,plain,(
% 3.23/1.00    ~v1_xboole_0(sK4)),
% 3.23/1.00    inference(cnf_transformation,[],[f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f55,plain,(
% 3.23/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.23/1.00    inference(cnf_transformation,[],[f36])).
% 3.23/1.00  
% 3.23/1.00  fof(f92,plain,(
% 3.23/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.23/1.00    inference(equality_resolution,[],[f55])).
% 3.23/1.00  
% 3.23/1.00  fof(f93,plain,(
% 3.23/1.00    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.23/1.00    inference(equality_resolution,[],[f92])).
% 3.23/1.00  
% 3.23/1.00  cnf(c_722,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2045,plain,
% 3.23/1.00      ( X0 != X1 | X0 = sK0(sK4) | sK0(sK4) != X1 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_722]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6952,plain,
% 3.23/1.00      ( X0 = sK0(sK4) | X0 != sK4 | sK0(sK4) != sK4 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2045]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6954,plain,
% 3.23/1.00      ( sK0(sK4) != sK4 | k1_xboole_0 = sK0(sK4) | k1_xboole_0 != sK4 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_6952]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_8,plain,
% 3.23/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4668,plain,
% 3.23/1.00      ( r1_tarski(k1_xboole_0,k1_tarski(sK4)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4414,plain,
% 3.23/1.00      ( r1_tarski(k1_xboole_0,k1_tarski(sK5)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_0,plain,
% 3.23/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_30,negated_conjecture,
% 3.23/1.00      ( ~ v1_xboole_0(sK5) ),
% 3.23/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_345,plain,
% 3.23/1.00      ( r2_hidden(sK0(X0),X0) | sK5 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_346,plain,
% 3.23/1.00      ( r2_hidden(sK0(sK5),sK5) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_345]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1087,plain,
% 3.23/1.00      ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_23,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,X1)
% 3.23/1.00      | v1_xboole_0(X1)
% 3.23/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_26,plain,
% 3.23/1.00      ( m1_subset_1(sK3(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_296,plain,
% 3.23/1.00      ( ~ v1_zfmisc_1(X0)
% 3.23/1.00      | v1_xboole_0(X1)
% 3.23/1.00      | v1_xboole_0(X0)
% 3.23/1.00      | X0 != X1
% 3.23/1.00      | k6_domain_1(X1,X2) = k1_tarski(X2)
% 3.23/1.00      | sK3(X0) != X2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_297,plain,
% 3.23/1.00      ( ~ v1_zfmisc_1(X0)
% 3.23/1.00      | v1_xboole_0(X0)
% 3.23/1.00      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_296]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_29,negated_conjecture,
% 3.23/1.00      ( v1_zfmisc_1(sK5) ),
% 3.23/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_315,plain,
% 3.23/1.00      ( v1_xboole_0(X0)
% 3.23/1.00      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
% 3.23/1.00      | sK5 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_297,c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_316,plain,
% 3.23/1.00      ( v1_xboole_0(sK5)
% 3.23/1.00      | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_315]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_318,plain,
% 3.23/1.00      ( k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_316,c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_25,plain,
% 3.23/1.00      ( ~ v1_zfmisc_1(X0)
% 3.23/1.00      | v1_xboole_0(X0)
% 3.23/1.00      | k6_domain_1(X0,sK3(X0)) = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_323,plain,
% 3.23/1.00      ( v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | sK5 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_324,plain,
% 3.23/1.00      ( v1_xboole_0(sK5) | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_326,plain,
% 3.23/1.00      ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_324,c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1114,plain,
% 3.23/1.00      ( k1_tarski(sK3(sK5)) = sK5 ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_318,c_326]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_13,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.23/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1090,plain,
% 3.23/1.00      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1961,plain,
% 3.23/1.00      ( sK3(sK5) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1114,c_1090]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2117,plain,
% 3.23/1.00      ( sK3(sK5) = sK0(sK5) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1087,c_1961]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2133,plain,
% 3.23/1.00      ( k1_tarski(sK0(sK5)) = sK5 ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_2117,c_1114]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_28,negated_conjecture,
% 3.23/1.00      ( r1_tarski(sK4,sK5) ),
% 3.23/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1089,plain,
% 3.23/1.00      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1096,plain,
% 3.23/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.23/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2281,plain,
% 3.23/1.00      ( k4_xboole_0(sK4,sK5) = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1089,c_1096]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_9,plain,
% 3.23/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 3.23/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2878,plain,
% 3.23/1.00      ( k3_tarski(k2_enumset1(sK5,sK5,sK5,sK4)) = k3_tarski(k2_enumset1(sK5,sK5,sK5,k1_xboole_0)) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2281,c_9]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7,plain,
% 3.23/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2880,plain,
% 3.23/1.00      ( k3_tarski(k2_enumset1(sK5,sK5,sK5,sK4)) = sK5 ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_2878,c_7]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_14,plain,
% 3.23/1.00      ( k1_tarski(X0) = X1
% 3.23/1.00      | k3_tarski(k2_enumset1(X2,X2,X2,X1)) != k1_tarski(X0)
% 3.23/1.00      | k1_xboole_0 = X1 ),
% 3.23/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2945,plain,
% 3.23/1.00      ( k1_tarski(X0) != sK5 | k1_tarski(X0) = sK4 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2880,c_14]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3115,plain,
% 3.23/1.00      ( k1_tarski(sK0(sK5)) = sK4 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2133,c_2945]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3116,plain,
% 3.23/1.00      ( sK5 = sK4 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_3115,c_2133]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_27,negated_conjecture,
% 3.23/1.00      ( sK4 != sK5 ),
% 3.23/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3214,plain,
% 3.23/1.00      ( sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3116,c_27]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1531,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,X1)
% 3.23/1.00      | ~ r2_hidden(sK0(sK4),X0)
% 3.23/1.00      | r2_hidden(sK0(sK4),X1) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3070,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,k1_tarski(sK4))
% 3.23/1.00      | ~ r2_hidden(sK0(sK4),X0)
% 3.23/1.00      | r2_hidden(sK0(sK4),k1_tarski(sK4)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1531]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3072,plain,
% 3.23/1.00      ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK4))
% 3.23/1.00      | r2_hidden(sK0(sK4),k1_tarski(sK4))
% 3.23/1.00      | ~ r2_hidden(sK0(sK4),k1_xboole_0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3070]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1475,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,k1_tarski(sK4)) | X0 = sK4 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2076,plain,
% 3.23/1.00      ( ~ r2_hidden(sK0(sK4),k1_tarski(sK4)) | sK0(sK4) = sK4 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1475]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1847,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,k1_tarski(sK5))
% 3.23/1.00      | ~ r2_hidden(X1,X0)
% 3.23/1.00      | r2_hidden(X1,k1_tarski(sK5)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1849,plain,
% 3.23/1.00      ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK5))
% 3.23/1.00      | r2_hidden(k1_xboole_0,k1_tarski(sK5))
% 3.23/1.00      | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1847]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_22,plain,
% 3.23/1.00      ( k3_tarski(k2_enumset1(k1_tarski(X0),k1_tarski(X0),k1_tarski(X0),X1)) != k1_xboole_0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1649,plain,
% 3.23/1.00      ( k3_tarski(k2_enumset1(sK5,sK5,sK5,X0)) != k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1114,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1827,plain,
% 3.23/1.00      ( sK5 != k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_7,c_1649]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1276,plain,
% 3.23/1.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_722]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1502,plain,
% 3.23/1.00      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1276]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1503,plain,
% 3.23/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1502]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1493,plain,
% 3.23/1.00      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_722]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1494,plain,
% 3.23/1.00      ( sK4 != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = sK4
% 3.23/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1493]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_721,plain,( X0 = X0 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1356,plain,
% 3.23/1.00      ( sK5 = sK5 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_721]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1343,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,k1_tarski(sK5)) | X0 = sK5 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1345,plain,
% 3.23/1.00      ( ~ r2_hidden(k1_xboole_0,k1_tarski(sK5)) | k1_xboole_0 = sK5 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1343]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_725,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/1.00      theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1315,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_725]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1317,plain,
% 3.23/1.00      ( r1_tarski(sK4,k1_xboole_0)
% 3.23/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.23/1.00      | sK4 != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1315]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_724,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/1.00      theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1254,plain,
% 3.23/1.00      ( r2_hidden(X0,X1)
% 3.23/1.00      | ~ r2_hidden(sK0(sK4),sK4)
% 3.23/1.00      | X0 != sK0(sK4)
% 3.23/1.00      | X1 != sK4 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_724]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1256,plain,
% 3.23/1.00      ( ~ r2_hidden(sK0(sK4),sK4)
% 3.23/1.00      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.23/1.00      | k1_xboole_0 != sK0(sK4)
% 3.23/1.00      | k1_xboole_0 != sK4 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1254]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1229,plain,
% 3.23/1.00      ( ~ r1_tarski(sK4,X0)
% 3.23/1.00      | r2_hidden(sK0(sK4),X0)
% 3.23/1.00      | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1231,plain,
% 3.23/1.00      ( ~ r1_tarski(sK4,k1_xboole_0)
% 3.23/1.00      | ~ r2_hidden(sK0(sK4),sK4)
% 3.23/1.00      | r2_hidden(sK0(sK4),k1_xboole_0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1229]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_31,negated_conjecture,
% 3.23/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.23/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_352,plain,
% 3.23/1.00      ( r2_hidden(sK0(X0),X0) | sK4 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_31]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_353,plain,
% 3.23/1.00      ( r2_hidden(sK0(sK4),sK4) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_352]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_65,plain,
% 3.23/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_12,plain,
% 3.23/1.00      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.23/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_55,plain,
% 3.23/1.00      ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_52,plain,
% 3.23/1.00      ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
% 3.23/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(contradiction,plain,
% 3.23/1.00      ( $false ),
% 3.23/1.00      inference(minisat,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_6954,c_4668,c_4414,c_3214,c_3072,c_2076,c_1849,c_1827,
% 3.23/1.00                 c_1503,c_1494,c_1356,c_1345,c_1317,c_1256,c_1231,c_353,
% 3.23/1.00                 c_65,c_55,c_52]) ).
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  ------                               Statistics
% 3.23/1.00  
% 3.23/1.00  ------ General
% 3.23/1.00  
% 3.23/1.00  abstr_ref_over_cycles:                  0
% 3.23/1.00  abstr_ref_under_cycles:                 0
% 3.23/1.00  gc_basic_clause_elim:                   0
% 3.23/1.00  forced_gc_time:                         0
% 3.23/1.00  parsing_time:                           0.009
% 3.23/1.00  unif_index_cands_time:                  0.
% 3.23/1.00  unif_index_add_time:                    0.
% 3.23/1.00  orderings_time:                         0.
% 3.23/1.00  out_proof_time:                         0.011
% 3.23/1.00  total_time:                             0.202
% 3.23/1.00  num_of_symbols:                         48
% 3.23/1.00  num_of_terms:                           5100
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing
% 3.23/1.00  
% 3.23/1.00  num_of_splits:                          0
% 3.23/1.00  num_of_split_atoms:                     0
% 3.23/1.00  num_of_reused_defs:                     0
% 3.23/1.00  num_eq_ax_congr_red:                    23
% 3.23/1.00  num_of_sem_filtered_clauses:            1
% 3.23/1.00  num_of_subtypes:                        0
% 3.23/1.00  monotx_restored_types:                  0
% 3.23/1.00  sat_num_of_epr_types:                   0
% 3.23/1.00  sat_num_of_non_cyclic_types:            0
% 3.23/1.00  sat_guarded_non_collapsed_types:        0
% 3.23/1.00  num_pure_diseq_elim:                    0
% 3.23/1.00  simp_replaced_by:                       0
% 3.23/1.00  res_preprocessed:                       121
% 3.23/1.00  prep_upred:                             0
% 3.23/1.00  prep_unflattend:                        25
% 3.23/1.00  smt_new_axioms:                         0
% 3.23/1.00  pred_elim_cands:                        2
% 3.23/1.00  pred_elim:                              3
% 3.23/1.00  pred_elim_cl:                           4
% 3.23/1.00  pred_elim_cycles:                       5
% 3.23/1.00  merged_defs:                            8
% 3.23/1.00  merged_defs_ncl:                        0
% 3.23/1.00  bin_hyper_res:                          8
% 3.23/1.00  prep_cycles:                            4
% 3.23/1.00  pred_elim_time:                         0.003
% 3.23/1.00  splitting_time:                         0.
% 3.23/1.00  sem_filter_time:                        0.
% 3.23/1.00  monotx_time:                            0.
% 3.23/1.00  subtype_inf_time:                       0.
% 3.23/1.00  
% 3.23/1.00  ------ Problem properties
% 3.23/1.00  
% 3.23/1.00  clauses:                                24
% 3.23/1.00  conjectures:                            2
% 3.23/1.00  epr:                                    4
% 3.23/1.00  horn:                                   18
% 3.23/1.00  ground:                                 6
% 3.23/1.00  unary:                                  11
% 3.23/1.00  binary:                                 6
% 3.23/1.00  lits:                                   44
% 3.23/1.00  lits_eq:                                25
% 3.23/1.00  fd_pure:                                0
% 3.23/1.00  fd_pseudo:                              0
% 3.23/1.00  fd_cond:                                0
% 3.23/1.00  fd_pseudo_cond:                         6
% 3.23/1.00  ac_symbols:                             0
% 3.23/1.00  
% 3.23/1.00  ------ Propositional Solver
% 3.23/1.00  
% 3.23/1.00  prop_solver_calls:                      27
% 3.23/1.00  prop_fast_solver_calls:                 755
% 3.23/1.00  smt_solver_calls:                       0
% 3.23/1.00  smt_fast_solver_calls:                  0
% 3.23/1.00  prop_num_of_clauses:                    2471
% 3.23/1.00  prop_preprocess_simplified:             7178
% 3.23/1.00  prop_fo_subsumed:                       9
% 3.23/1.00  prop_solver_time:                       0.
% 3.23/1.00  smt_solver_time:                        0.
% 3.23/1.00  smt_fast_solver_time:                   0.
% 3.23/1.00  prop_fast_solver_time:                  0.
% 3.23/1.00  prop_unsat_core_time:                   0.
% 3.23/1.00  
% 3.23/1.00  ------ QBF
% 3.23/1.00  
% 3.23/1.00  qbf_q_res:                              0
% 3.23/1.00  qbf_num_tautologies:                    0
% 3.23/1.00  qbf_prep_cycles:                        0
% 3.23/1.00  
% 3.23/1.00  ------ BMC1
% 3.23/1.00  
% 3.23/1.00  bmc1_current_bound:                     -1
% 3.23/1.00  bmc1_last_solved_bound:                 -1
% 3.23/1.00  bmc1_unsat_core_size:                   -1
% 3.23/1.00  bmc1_unsat_core_parents_size:           -1
% 3.23/1.00  bmc1_merge_next_fun:                    0
% 3.23/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation
% 3.23/1.00  
% 3.23/1.00  inst_num_of_clauses:                    808
% 3.23/1.00  inst_num_in_passive:                    331
% 3.23/1.00  inst_num_in_active:                     266
% 3.23/1.00  inst_num_in_unprocessed:                210
% 3.23/1.00  inst_num_of_loops:                      363
% 3.23/1.00  inst_num_of_learning_restarts:          0
% 3.23/1.00  inst_num_moves_active_passive:          95
% 3.23/1.00  inst_lit_activity:                      0
% 3.23/1.00  inst_lit_activity_moves:                0
% 3.23/1.00  inst_num_tautologies:                   0
% 3.23/1.00  inst_num_prop_implied:                  0
% 3.23/1.00  inst_num_existing_simplified:           0
% 3.23/1.00  inst_num_eq_res_simplified:             0
% 3.23/1.00  inst_num_child_elim:                    0
% 3.23/1.00  inst_num_of_dismatching_blockings:      472
% 3.23/1.00  inst_num_of_non_proper_insts:           787
% 3.23/1.00  inst_num_of_duplicates:                 0
% 3.23/1.00  inst_inst_num_from_inst_to_res:         0
% 3.23/1.00  inst_dismatching_checking_time:         0.
% 3.23/1.00  
% 3.23/1.00  ------ Resolution
% 3.23/1.00  
% 3.23/1.00  res_num_of_clauses:                     0
% 3.23/1.00  res_num_in_passive:                     0
% 3.23/1.00  res_num_in_active:                      0
% 3.23/1.00  res_num_of_loops:                       125
% 3.23/1.00  res_forward_subset_subsumed:            66
% 3.23/1.00  res_backward_subset_subsumed:           0
% 3.23/1.00  res_forward_subsumed:                   0
% 3.23/1.00  res_backward_subsumed:                  0
% 3.23/1.00  res_forward_subsumption_resolution:     0
% 3.23/1.00  res_backward_subsumption_resolution:    0
% 3.23/1.00  res_clause_to_clause_subsumption:       436
% 3.23/1.00  res_orphan_elimination:                 0
% 3.23/1.00  res_tautology_del:                      38
% 3.23/1.00  res_num_eq_res_simplified:              0
% 3.23/1.00  res_num_sel_changes:                    0
% 3.23/1.00  res_moves_from_active_to_pass:          0
% 3.23/1.00  
% 3.23/1.00  ------ Superposition
% 3.23/1.00  
% 3.23/1.00  sup_time_total:                         0.
% 3.23/1.00  sup_time_generating:                    0.
% 3.23/1.00  sup_time_sim_full:                      0.
% 3.23/1.00  sup_time_sim_immed:                     0.
% 3.23/1.00  
% 3.23/1.00  sup_num_of_clauses:                     101
% 3.23/1.00  sup_num_in_active:                      61
% 3.23/1.00  sup_num_in_passive:                     40
% 3.23/1.00  sup_num_of_loops:                       72
% 3.23/1.00  sup_fw_superposition:                   76
% 3.23/1.00  sup_bw_superposition:                   103
% 3.23/1.00  sup_immediate_simplified:               69
% 3.23/1.00  sup_given_eliminated:                   2
% 3.23/1.00  comparisons_done:                       0
% 3.23/1.00  comparisons_avoided:                    93
% 3.23/1.00  
% 3.23/1.00  ------ Simplifications
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  sim_fw_subset_subsumed:                 35
% 3.23/1.00  sim_bw_subset_subsumed:                 0
% 3.23/1.00  sim_fw_subsumed:                        19
% 3.23/1.00  sim_bw_subsumed:                        3
% 3.23/1.00  sim_fw_subsumption_res:                 0
% 3.23/1.00  sim_bw_subsumption_res:                 0
% 3.23/1.00  sim_tautology_del:                      5
% 3.23/1.00  sim_eq_tautology_del:                   13
% 3.23/1.00  sim_eq_res_simp:                        0
% 3.23/1.00  sim_fw_demodulated:                     2
% 3.23/1.00  sim_bw_demodulated:                     11
% 3.23/1.00  sim_light_normalised:                   12
% 3.23/1.00  sim_joinable_taut:                      0
% 3.23/1.00  sim_joinable_simp:                      0
% 3.23/1.00  sim_ac_normalised:                      0
% 3.23/1.00  sim_smt_subsumption:                    0
% 3.23/1.00  
%------------------------------------------------------------------------------
