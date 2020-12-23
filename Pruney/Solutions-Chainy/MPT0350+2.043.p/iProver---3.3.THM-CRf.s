%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:12 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  151 (1188 expanded)
%              Number of clauses        :   83 ( 399 expanded)
%              Number of leaves         :   22 ( 326 expanded)
%              Depth                    :   21
%              Number of atoms          :  282 (1395 expanded)
%              Number of equality atoms :  140 (1175 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f93,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f91,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f53,f57,f57,f57])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f57,f57])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f45])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f60,f57])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f23,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1014,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_2])).

cnf(c_2565,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_10,c_1014])).

cnf(c_2605,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2565])).

cnf(c_1143,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_2])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1364,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_1370,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1364,c_10])).

cnf(c_1366,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_1368,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1366,c_8])).

cnf(c_1371,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1370,c_1368])).

cnf(c_1531,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1371,c_11])).

cnf(c_1530,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1371,c_11])).

cnf(c_1532,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1530,c_1143])).

cnf(c_2044,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1531,c_1532])).

cnf(c_2053,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2044,c_10])).

cnf(c_2155,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_2053,c_2053])).

cnf(c_2278,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2155])).

cnf(c_2653,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2605,c_1143,c_2278])).

cnf(c_6,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_9502,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2653,c_6])).

cnf(c_9575,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_9502,c_2653])).

cnf(c_1853,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1859,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_1853,c_0])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2036,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_1532])).

cnf(c_3150,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2036,c_0])).

cnf(c_1384,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_6054,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3150,c_1384])).

cnf(c_6060,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6054,c_1371])).

cnf(c_6365,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_6060])).

cnf(c_9576,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9575,c_1859,c_6365])).

cnf(c_2151,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1532,c_2053])).

cnf(c_3115,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1384,c_2151])).

cnf(c_13652,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_9576,c_3115])).

cnf(c_13673,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13652,c_1143,c_1370,c_6060])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_992,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_989,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_119,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_4])).

cnf(c_120,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_119])).

cnf(c_980,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120])).

cnf(c_9655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_980])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_981,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_subset_1(X1,X0,X2) ),
    inference(theory_normalisation,[status(thm)],[c_24,c_11,c_2])).

cnf(c_982,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_1766,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_982,c_1384])).

cnf(c_1770,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(X0,sK3)) = k4_subset_1(sK2,sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_981,c_1766])).

cnf(c_23964,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(X0,sK3)) = k4_subset_1(sK2,sK3,X0)
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9655,c_1770])).

cnf(c_24867,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = k4_subset_1(sK2,sK3,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_992,c_23964])).

cnf(c_24882,plain,
    ( k4_subset_1(sK2,sK3,k4_xboole_0(sK2,sK3)) = k5_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_13673,c_24867])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_985,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2448,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_981,c_985])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2804,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2448,c_33])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_988,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7872,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_988])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_993,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20485,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_7872,c_993])).

cnf(c_3120,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1384,c_2053])).

cnf(c_20721,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_20485,c_3120])).

cnf(c_25012,plain,
    ( k4_subset_1(sK2,sK3,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_24882,c_20721])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_984,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_22128,plain,
    ( k3_subset_1(sK2,sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_981,c_984])).

cnf(c_25,negated_conjecture,
    ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_21,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_996,plain,
    ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3)) != sK2 ),
    inference(demodulation,[status(thm)],[c_25,c_21])).

cnf(c_22133,plain,
    ( k4_subset_1(sK2,sK3,k4_xboole_0(sK2,sK3)) != sK2 ),
    inference(demodulation,[status(thm)],[c_22128,c_996])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25012,c_22133])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.76/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/1.51  
% 7.76/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.51  
% 7.76/1.51  ------  iProver source info
% 7.76/1.51  
% 7.76/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.51  git: non_committed_changes: false
% 7.76/1.51  git: last_make_outside_of_git: false
% 7.76/1.51  
% 7.76/1.51  ------ 
% 7.76/1.51  
% 7.76/1.51  ------ Input Options
% 7.76/1.51  
% 7.76/1.51  --out_options                           all
% 7.76/1.51  --tptp_safe_out                         true
% 7.76/1.51  --problem_path                          ""
% 7.76/1.51  --include_path                          ""
% 7.76/1.51  --clausifier                            res/vclausify_rel
% 7.76/1.51  --clausifier_options                    ""
% 7.76/1.51  --stdin                                 false
% 7.76/1.51  --stats_out                             all
% 7.76/1.51  
% 7.76/1.51  ------ General Options
% 7.76/1.51  
% 7.76/1.51  --fof                                   false
% 7.76/1.51  --time_out_real                         305.
% 7.76/1.51  --time_out_virtual                      -1.
% 7.76/1.51  --symbol_type_check                     false
% 7.76/1.51  --clausify_out                          false
% 7.76/1.51  --sig_cnt_out                           false
% 7.76/1.51  --trig_cnt_out                          false
% 7.76/1.51  --trig_cnt_out_tolerance                1.
% 7.76/1.51  --trig_cnt_out_sk_spl                   false
% 7.76/1.51  --abstr_cl_out                          false
% 7.76/1.51  
% 7.76/1.51  ------ Global Options
% 7.76/1.51  
% 7.76/1.51  --schedule                              default
% 7.76/1.51  --add_important_lit                     false
% 7.76/1.51  --prop_solver_per_cl                    1000
% 7.76/1.51  --min_unsat_core                        false
% 7.76/1.51  --soft_assumptions                      false
% 7.76/1.51  --soft_lemma_size                       3
% 7.76/1.51  --prop_impl_unit_size                   0
% 7.76/1.51  --prop_impl_unit                        []
% 7.76/1.51  --share_sel_clauses                     true
% 7.76/1.51  --reset_solvers                         false
% 7.76/1.51  --bc_imp_inh                            [conj_cone]
% 7.76/1.51  --conj_cone_tolerance                   3.
% 7.76/1.51  --extra_neg_conj                        none
% 7.76/1.51  --large_theory_mode                     true
% 7.76/1.51  --prolific_symb_bound                   200
% 7.76/1.51  --lt_threshold                          2000
% 7.76/1.51  --clause_weak_htbl                      true
% 7.76/1.51  --gc_record_bc_elim                     false
% 7.76/1.51  
% 7.76/1.51  ------ Preprocessing Options
% 7.76/1.51  
% 7.76/1.51  --preprocessing_flag                    true
% 7.76/1.51  --time_out_prep_mult                    0.1
% 7.76/1.51  --splitting_mode                        input
% 7.76/1.51  --splitting_grd                         true
% 7.76/1.51  --splitting_cvd                         false
% 7.76/1.51  --splitting_cvd_svl                     false
% 7.76/1.51  --splitting_nvd                         32
% 7.76/1.51  --sub_typing                            true
% 7.76/1.51  --prep_gs_sim                           true
% 7.76/1.51  --prep_unflatten                        true
% 7.76/1.51  --prep_res_sim                          true
% 7.76/1.51  --prep_upred                            true
% 7.76/1.51  --prep_sem_filter                       exhaustive
% 7.76/1.51  --prep_sem_filter_out                   false
% 7.76/1.51  --pred_elim                             true
% 7.76/1.51  --res_sim_input                         true
% 7.76/1.51  --eq_ax_congr_red                       true
% 7.76/1.51  --pure_diseq_elim                       true
% 7.76/1.51  --brand_transform                       false
% 7.76/1.51  --non_eq_to_eq                          false
% 7.76/1.51  --prep_def_merge                        true
% 7.76/1.51  --prep_def_merge_prop_impl              false
% 7.76/1.51  --prep_def_merge_mbd                    true
% 7.76/1.51  --prep_def_merge_tr_red                 false
% 7.76/1.51  --prep_def_merge_tr_cl                  false
% 7.76/1.51  --smt_preprocessing                     true
% 7.76/1.51  --smt_ac_axioms                         fast
% 7.76/1.51  --preprocessed_out                      false
% 7.76/1.51  --preprocessed_stats                    false
% 7.76/1.51  
% 7.76/1.51  ------ Abstraction refinement Options
% 7.76/1.51  
% 7.76/1.51  --abstr_ref                             []
% 7.76/1.51  --abstr_ref_prep                        false
% 7.76/1.51  --abstr_ref_until_sat                   false
% 7.76/1.51  --abstr_ref_sig_restrict                funpre
% 7.76/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.51  --abstr_ref_under                       []
% 7.76/1.51  
% 7.76/1.51  ------ SAT Options
% 7.76/1.51  
% 7.76/1.51  --sat_mode                              false
% 7.76/1.51  --sat_fm_restart_options                ""
% 7.76/1.51  --sat_gr_def                            false
% 7.76/1.51  --sat_epr_types                         true
% 7.76/1.51  --sat_non_cyclic_types                  false
% 7.76/1.51  --sat_finite_models                     false
% 7.76/1.51  --sat_fm_lemmas                         false
% 7.76/1.51  --sat_fm_prep                           false
% 7.76/1.51  --sat_fm_uc_incr                        true
% 7.76/1.51  --sat_out_model                         small
% 7.76/1.51  --sat_out_clauses                       false
% 7.76/1.51  
% 7.76/1.51  ------ QBF Options
% 7.76/1.51  
% 7.76/1.51  --qbf_mode                              false
% 7.76/1.51  --qbf_elim_univ                         false
% 7.76/1.51  --qbf_dom_inst                          none
% 7.76/1.51  --qbf_dom_pre_inst                      false
% 7.76/1.51  --qbf_sk_in                             false
% 7.76/1.51  --qbf_pred_elim                         true
% 7.76/1.51  --qbf_split                             512
% 7.76/1.51  
% 7.76/1.51  ------ BMC1 Options
% 7.76/1.51  
% 7.76/1.51  --bmc1_incremental                      false
% 7.76/1.51  --bmc1_axioms                           reachable_all
% 7.76/1.51  --bmc1_min_bound                        0
% 7.76/1.51  --bmc1_max_bound                        -1
% 7.76/1.51  --bmc1_max_bound_default                -1
% 7.76/1.51  --bmc1_symbol_reachability              true
% 7.76/1.51  --bmc1_property_lemmas                  false
% 7.76/1.51  --bmc1_k_induction                      false
% 7.76/1.51  --bmc1_non_equiv_states                 false
% 7.76/1.51  --bmc1_deadlock                         false
% 7.76/1.51  --bmc1_ucm                              false
% 7.76/1.51  --bmc1_add_unsat_core                   none
% 7.76/1.51  --bmc1_unsat_core_children              false
% 7.76/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.51  --bmc1_out_stat                         full
% 7.76/1.51  --bmc1_ground_init                      false
% 7.76/1.51  --bmc1_pre_inst_next_state              false
% 7.76/1.51  --bmc1_pre_inst_state                   false
% 7.76/1.51  --bmc1_pre_inst_reach_state             false
% 7.76/1.51  --bmc1_out_unsat_core                   false
% 7.76/1.51  --bmc1_aig_witness_out                  false
% 7.76/1.51  --bmc1_verbose                          false
% 7.76/1.51  --bmc1_dump_clauses_tptp                false
% 7.76/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.51  --bmc1_dump_file                        -
% 7.76/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.51  --bmc1_ucm_extend_mode                  1
% 7.76/1.51  --bmc1_ucm_init_mode                    2
% 7.76/1.51  --bmc1_ucm_cone_mode                    none
% 7.76/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.51  --bmc1_ucm_relax_model                  4
% 7.76/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.51  --bmc1_ucm_layered_model                none
% 7.76/1.51  --bmc1_ucm_max_lemma_size               10
% 7.76/1.51  
% 7.76/1.51  ------ AIG Options
% 7.76/1.51  
% 7.76/1.51  --aig_mode                              false
% 7.76/1.51  
% 7.76/1.51  ------ Instantiation Options
% 7.76/1.51  
% 7.76/1.51  --instantiation_flag                    true
% 7.76/1.51  --inst_sos_flag                         true
% 7.76/1.51  --inst_sos_phase                        true
% 7.76/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.51  --inst_lit_sel_side                     num_symb
% 7.76/1.51  --inst_solver_per_active                1400
% 7.76/1.51  --inst_solver_calls_frac                1.
% 7.76/1.51  --inst_passive_queue_type               priority_queues
% 7.76/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.51  --inst_passive_queues_freq              [25;2]
% 7.76/1.51  --inst_dismatching                      true
% 7.76/1.51  --inst_eager_unprocessed_to_passive     true
% 7.76/1.51  --inst_prop_sim_given                   true
% 7.76/1.51  --inst_prop_sim_new                     false
% 7.76/1.51  --inst_subs_new                         false
% 7.76/1.51  --inst_eq_res_simp                      false
% 7.76/1.51  --inst_subs_given                       false
% 7.76/1.51  --inst_orphan_elimination               true
% 7.76/1.51  --inst_learning_loop_flag               true
% 7.76/1.51  --inst_learning_start                   3000
% 7.76/1.51  --inst_learning_factor                  2
% 7.76/1.51  --inst_start_prop_sim_after_learn       3
% 7.76/1.51  --inst_sel_renew                        solver
% 7.76/1.51  --inst_lit_activity_flag                true
% 7.76/1.51  --inst_restr_to_given                   false
% 7.76/1.51  --inst_activity_threshold               500
% 7.76/1.51  --inst_out_proof                        true
% 7.76/1.51  
% 7.76/1.51  ------ Resolution Options
% 7.76/1.51  
% 7.76/1.51  --resolution_flag                       true
% 7.76/1.51  --res_lit_sel                           adaptive
% 7.76/1.51  --res_lit_sel_side                      none
% 7.76/1.51  --res_ordering                          kbo
% 7.76/1.51  --res_to_prop_solver                    active
% 7.76/1.51  --res_prop_simpl_new                    false
% 7.76/1.51  --res_prop_simpl_given                  true
% 7.76/1.51  --res_passive_queue_type                priority_queues
% 7.76/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.51  --res_passive_queues_freq               [15;5]
% 7.76/1.51  --res_forward_subs                      full
% 7.76/1.51  --res_backward_subs                     full
% 7.76/1.51  --res_forward_subs_resolution           true
% 7.76/1.51  --res_backward_subs_resolution          true
% 7.76/1.51  --res_orphan_elimination                true
% 7.76/1.51  --res_time_limit                        2.
% 7.76/1.51  --res_out_proof                         true
% 7.76/1.51  
% 7.76/1.51  ------ Superposition Options
% 7.76/1.51  
% 7.76/1.51  --superposition_flag                    true
% 7.76/1.51  --sup_passive_queue_type                priority_queues
% 7.76/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.51  --demod_completeness_check              fast
% 7.76/1.51  --demod_use_ground                      true
% 7.76/1.51  --sup_to_prop_solver                    passive
% 7.76/1.51  --sup_prop_simpl_new                    true
% 7.76/1.51  --sup_prop_simpl_given                  true
% 7.76/1.51  --sup_fun_splitting                     true
% 7.76/1.51  --sup_smt_interval                      50000
% 7.76/1.51  
% 7.76/1.51  ------ Superposition Simplification Setup
% 7.76/1.51  
% 7.76/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.51  --sup_immed_triv                        [TrivRules]
% 7.76/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.51  --sup_immed_bw_main                     []
% 7.76/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.51  --sup_input_bw                          []
% 7.76/1.51  
% 7.76/1.51  ------ Combination Options
% 7.76/1.51  
% 7.76/1.51  --comb_res_mult                         3
% 7.76/1.51  --comb_sup_mult                         2
% 7.76/1.51  --comb_inst_mult                        10
% 7.76/1.51  
% 7.76/1.51  ------ Debug Options
% 7.76/1.51  
% 7.76/1.51  --dbg_backtrace                         false
% 7.76/1.51  --dbg_dump_prop_clauses                 false
% 7.76/1.51  --dbg_dump_prop_clauses_file            -
% 7.76/1.51  --dbg_out_stat                          false
% 7.76/1.51  ------ Parsing...
% 7.76/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.51  
% 7.76/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.76/1.51  
% 7.76/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.51  
% 7.76/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.51  ------ Proving...
% 7.76/1.51  ------ Problem Properties 
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  clauses                                 27
% 7.76/1.51  conjectures                             2
% 7.76/1.51  EPR                                     5
% 7.76/1.51  Horn                                    24
% 7.76/1.51  unary                                   14
% 7.76/1.51  binary                                  7
% 7.76/1.51  lits                                    46
% 7.76/1.51  lits eq                                 16
% 7.76/1.51  fd_pure                                 0
% 7.76/1.51  fd_pseudo                               0
% 7.76/1.51  fd_cond                                 0
% 7.76/1.51  fd_pseudo_cond                          2
% 7.76/1.51  AC symbols                              1
% 7.76/1.51  
% 7.76/1.51  ------ Schedule dynamic 5 is on 
% 7.76/1.51  
% 7.76/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  ------ 
% 7.76/1.51  Current options:
% 7.76/1.51  ------ 
% 7.76/1.51  
% 7.76/1.51  ------ Input Options
% 7.76/1.51  
% 7.76/1.51  --out_options                           all
% 7.76/1.51  --tptp_safe_out                         true
% 7.76/1.51  --problem_path                          ""
% 7.76/1.51  --include_path                          ""
% 7.76/1.51  --clausifier                            res/vclausify_rel
% 7.76/1.51  --clausifier_options                    ""
% 7.76/1.51  --stdin                                 false
% 7.76/1.51  --stats_out                             all
% 7.76/1.51  
% 7.76/1.51  ------ General Options
% 7.76/1.51  
% 7.76/1.51  --fof                                   false
% 7.76/1.51  --time_out_real                         305.
% 7.76/1.51  --time_out_virtual                      -1.
% 7.76/1.51  --symbol_type_check                     false
% 7.76/1.51  --clausify_out                          false
% 7.76/1.51  --sig_cnt_out                           false
% 7.76/1.51  --trig_cnt_out                          false
% 7.76/1.51  --trig_cnt_out_tolerance                1.
% 7.76/1.51  --trig_cnt_out_sk_spl                   false
% 7.76/1.51  --abstr_cl_out                          false
% 7.76/1.51  
% 7.76/1.51  ------ Global Options
% 7.76/1.51  
% 7.76/1.51  --schedule                              default
% 7.76/1.51  --add_important_lit                     false
% 7.76/1.51  --prop_solver_per_cl                    1000
% 7.76/1.51  --min_unsat_core                        false
% 7.76/1.51  --soft_assumptions                      false
% 7.76/1.51  --soft_lemma_size                       3
% 7.76/1.51  --prop_impl_unit_size                   0
% 7.76/1.51  --prop_impl_unit                        []
% 7.76/1.51  --share_sel_clauses                     true
% 7.76/1.51  --reset_solvers                         false
% 7.76/1.51  --bc_imp_inh                            [conj_cone]
% 7.76/1.51  --conj_cone_tolerance                   3.
% 7.76/1.51  --extra_neg_conj                        none
% 7.76/1.51  --large_theory_mode                     true
% 7.76/1.51  --prolific_symb_bound                   200
% 7.76/1.51  --lt_threshold                          2000
% 7.76/1.51  --clause_weak_htbl                      true
% 7.76/1.51  --gc_record_bc_elim                     false
% 7.76/1.51  
% 7.76/1.51  ------ Preprocessing Options
% 7.76/1.51  
% 7.76/1.51  --preprocessing_flag                    true
% 7.76/1.51  --time_out_prep_mult                    0.1
% 7.76/1.51  --splitting_mode                        input
% 7.76/1.51  --splitting_grd                         true
% 7.76/1.51  --splitting_cvd                         false
% 7.76/1.51  --splitting_cvd_svl                     false
% 7.76/1.51  --splitting_nvd                         32
% 7.76/1.51  --sub_typing                            true
% 7.76/1.51  --prep_gs_sim                           true
% 7.76/1.51  --prep_unflatten                        true
% 7.76/1.51  --prep_res_sim                          true
% 7.76/1.51  --prep_upred                            true
% 7.76/1.51  --prep_sem_filter                       exhaustive
% 7.76/1.51  --prep_sem_filter_out                   false
% 7.76/1.51  --pred_elim                             true
% 7.76/1.51  --res_sim_input                         true
% 7.76/1.51  --eq_ax_congr_red                       true
% 7.76/1.51  --pure_diseq_elim                       true
% 7.76/1.51  --brand_transform                       false
% 7.76/1.51  --non_eq_to_eq                          false
% 7.76/1.51  --prep_def_merge                        true
% 7.76/1.51  --prep_def_merge_prop_impl              false
% 7.76/1.51  --prep_def_merge_mbd                    true
% 7.76/1.51  --prep_def_merge_tr_red                 false
% 7.76/1.51  --prep_def_merge_tr_cl                  false
% 7.76/1.51  --smt_preprocessing                     true
% 7.76/1.51  --smt_ac_axioms                         fast
% 7.76/1.51  --preprocessed_out                      false
% 7.76/1.51  --preprocessed_stats                    false
% 7.76/1.51  
% 7.76/1.51  ------ Abstraction refinement Options
% 7.76/1.51  
% 7.76/1.51  --abstr_ref                             []
% 7.76/1.51  --abstr_ref_prep                        false
% 7.76/1.51  --abstr_ref_until_sat                   false
% 7.76/1.51  --abstr_ref_sig_restrict                funpre
% 7.76/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.51  --abstr_ref_under                       []
% 7.76/1.51  
% 7.76/1.51  ------ SAT Options
% 7.76/1.51  
% 7.76/1.51  --sat_mode                              false
% 7.76/1.51  --sat_fm_restart_options                ""
% 7.76/1.51  --sat_gr_def                            false
% 7.76/1.51  --sat_epr_types                         true
% 7.76/1.51  --sat_non_cyclic_types                  false
% 7.76/1.51  --sat_finite_models                     false
% 7.76/1.51  --sat_fm_lemmas                         false
% 7.76/1.51  --sat_fm_prep                           false
% 7.76/1.51  --sat_fm_uc_incr                        true
% 7.76/1.51  --sat_out_model                         small
% 7.76/1.51  --sat_out_clauses                       false
% 7.76/1.51  
% 7.76/1.51  ------ QBF Options
% 7.76/1.51  
% 7.76/1.51  --qbf_mode                              false
% 7.76/1.51  --qbf_elim_univ                         false
% 7.76/1.51  --qbf_dom_inst                          none
% 7.76/1.51  --qbf_dom_pre_inst                      false
% 7.76/1.51  --qbf_sk_in                             false
% 7.76/1.51  --qbf_pred_elim                         true
% 7.76/1.51  --qbf_split                             512
% 7.76/1.51  
% 7.76/1.51  ------ BMC1 Options
% 7.76/1.51  
% 7.76/1.51  --bmc1_incremental                      false
% 7.76/1.51  --bmc1_axioms                           reachable_all
% 7.76/1.51  --bmc1_min_bound                        0
% 7.76/1.51  --bmc1_max_bound                        -1
% 7.76/1.51  --bmc1_max_bound_default                -1
% 7.76/1.51  --bmc1_symbol_reachability              true
% 7.76/1.51  --bmc1_property_lemmas                  false
% 7.76/1.51  --bmc1_k_induction                      false
% 7.76/1.51  --bmc1_non_equiv_states                 false
% 7.76/1.51  --bmc1_deadlock                         false
% 7.76/1.51  --bmc1_ucm                              false
% 7.76/1.51  --bmc1_add_unsat_core                   none
% 7.76/1.51  --bmc1_unsat_core_children              false
% 7.76/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.51  --bmc1_out_stat                         full
% 7.76/1.51  --bmc1_ground_init                      false
% 7.76/1.51  --bmc1_pre_inst_next_state              false
% 7.76/1.51  --bmc1_pre_inst_state                   false
% 7.76/1.51  --bmc1_pre_inst_reach_state             false
% 7.76/1.51  --bmc1_out_unsat_core                   false
% 7.76/1.51  --bmc1_aig_witness_out                  false
% 7.76/1.51  --bmc1_verbose                          false
% 7.76/1.51  --bmc1_dump_clauses_tptp                false
% 7.76/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.51  --bmc1_dump_file                        -
% 7.76/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.51  --bmc1_ucm_extend_mode                  1
% 7.76/1.51  --bmc1_ucm_init_mode                    2
% 7.76/1.51  --bmc1_ucm_cone_mode                    none
% 7.76/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.51  --bmc1_ucm_relax_model                  4
% 7.76/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.51  --bmc1_ucm_layered_model                none
% 7.76/1.51  --bmc1_ucm_max_lemma_size               10
% 7.76/1.51  
% 7.76/1.51  ------ AIG Options
% 7.76/1.51  
% 7.76/1.51  --aig_mode                              false
% 7.76/1.51  
% 7.76/1.51  ------ Instantiation Options
% 7.76/1.51  
% 7.76/1.51  --instantiation_flag                    true
% 7.76/1.51  --inst_sos_flag                         true
% 7.76/1.51  --inst_sos_phase                        true
% 7.76/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.51  --inst_lit_sel_side                     none
% 7.76/1.51  --inst_solver_per_active                1400
% 7.76/1.51  --inst_solver_calls_frac                1.
% 7.76/1.51  --inst_passive_queue_type               priority_queues
% 7.76/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.51  --inst_passive_queues_freq              [25;2]
% 7.76/1.51  --inst_dismatching                      true
% 7.76/1.51  --inst_eager_unprocessed_to_passive     true
% 7.76/1.51  --inst_prop_sim_given                   true
% 7.76/1.51  --inst_prop_sim_new                     false
% 7.76/1.51  --inst_subs_new                         false
% 7.76/1.51  --inst_eq_res_simp                      false
% 7.76/1.51  --inst_subs_given                       false
% 7.76/1.51  --inst_orphan_elimination               true
% 7.76/1.51  --inst_learning_loop_flag               true
% 7.76/1.51  --inst_learning_start                   3000
% 7.76/1.51  --inst_learning_factor                  2
% 7.76/1.51  --inst_start_prop_sim_after_learn       3
% 7.76/1.51  --inst_sel_renew                        solver
% 7.76/1.51  --inst_lit_activity_flag                true
% 7.76/1.51  --inst_restr_to_given                   false
% 7.76/1.51  --inst_activity_threshold               500
% 7.76/1.51  --inst_out_proof                        true
% 7.76/1.51  
% 7.76/1.51  ------ Resolution Options
% 7.76/1.51  
% 7.76/1.51  --resolution_flag                       false
% 7.76/1.51  --res_lit_sel                           adaptive
% 7.76/1.51  --res_lit_sel_side                      none
% 7.76/1.51  --res_ordering                          kbo
% 7.76/1.51  --res_to_prop_solver                    active
% 7.76/1.51  --res_prop_simpl_new                    false
% 7.76/1.51  --res_prop_simpl_given                  true
% 7.76/1.51  --res_passive_queue_type                priority_queues
% 7.76/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.51  --res_passive_queues_freq               [15;5]
% 7.76/1.51  --res_forward_subs                      full
% 7.76/1.51  --res_backward_subs                     full
% 7.76/1.51  --res_forward_subs_resolution           true
% 7.76/1.51  --res_backward_subs_resolution          true
% 7.76/1.51  --res_orphan_elimination                true
% 7.76/1.51  --res_time_limit                        2.
% 7.76/1.51  --res_out_proof                         true
% 7.76/1.51  
% 7.76/1.51  ------ Superposition Options
% 7.76/1.51  
% 7.76/1.51  --superposition_flag                    true
% 7.76/1.51  --sup_passive_queue_type                priority_queues
% 7.76/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.51  --demod_completeness_check              fast
% 7.76/1.51  --demod_use_ground                      true
% 7.76/1.51  --sup_to_prop_solver                    passive
% 7.76/1.51  --sup_prop_simpl_new                    true
% 7.76/1.51  --sup_prop_simpl_given                  true
% 7.76/1.51  --sup_fun_splitting                     true
% 7.76/1.51  --sup_smt_interval                      50000
% 7.76/1.51  
% 7.76/1.51  ------ Superposition Simplification Setup
% 7.76/1.51  
% 7.76/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.51  --sup_immed_triv                        [TrivRules]
% 7.76/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.51  --sup_immed_bw_main                     []
% 7.76/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.51  --sup_input_bw                          []
% 7.76/1.51  
% 7.76/1.51  ------ Combination Options
% 7.76/1.51  
% 7.76/1.51  --comb_res_mult                         3
% 7.76/1.51  --comb_sup_mult                         2
% 7.76/1.51  --comb_inst_mult                        10
% 7.76/1.51  
% 7.76/1.51  ------ Debug Options
% 7.76/1.51  
% 7.76/1.51  --dbg_backtrace                         false
% 7.76/1.51  --dbg_dump_prop_clauses                 false
% 7.76/1.51  --dbg_dump_prop_clauses_file            -
% 7.76/1.51  --dbg_out_stat                          false
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  ------ Proving...
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  % SZS status Theorem for theBenchmark.p
% 7.76/1.51  
% 7.76/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.51  
% 7.76/1.51  fof(f5,axiom,(
% 7.76/1.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f52,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f5])).
% 7.76/1.51  
% 7.76/1.51  fof(f10,axiom,(
% 7.76/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f57,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.76/1.51    inference(cnf_transformation,[],[f10])).
% 7.76/1.51  
% 7.76/1.51  fof(f88,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 7.76/1.51    inference(definition_unfolding,[],[f52,f57])).
% 7.76/1.51  
% 7.76/1.51  fof(f11,axiom,(
% 7.76/1.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f58,plain,(
% 7.76/1.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.76/1.51    inference(cnf_transformation,[],[f11])).
% 7.76/1.51  
% 7.76/1.51  fof(f12,axiom,(
% 7.76/1.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f59,plain,(
% 7.76/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f12])).
% 7.76/1.51  
% 7.76/1.51  fof(f2,axiom,(
% 7.76/1.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f48,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f2])).
% 7.76/1.51  
% 7.76/1.51  fof(f8,axiom,(
% 7.76/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f55,plain,(
% 7.76/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.76/1.51    inference(cnf_transformation,[],[f8])).
% 7.76/1.51  
% 7.76/1.51  fof(f93,plain,(
% 7.76/1.51    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.76/1.51    inference(definition_unfolding,[],[f55,f57])).
% 7.76/1.51  
% 7.76/1.51  fof(f6,axiom,(
% 7.76/1.51    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f53,plain,(
% 7.76/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 7.76/1.51    inference(cnf_transformation,[],[f6])).
% 7.76/1.51  
% 7.76/1.51  fof(f91,plain,(
% 7.76/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1))) )),
% 7.76/1.51    inference(definition_unfolding,[],[f53,f57,f57,f57])).
% 7.76/1.51  
% 7.76/1.51  fof(f1,axiom,(
% 7.76/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f47,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f1])).
% 7.76/1.51  
% 7.76/1.51  fof(f89,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.76/1.51    inference(definition_unfolding,[],[f47,f57,f57])).
% 7.76/1.51  
% 7.76/1.51  fof(f9,axiom,(
% 7.76/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f56,plain,(
% 7.76/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f9])).
% 7.76/1.51  
% 7.76/1.51  fof(f20,axiom,(
% 7.76/1.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f40,plain,(
% 7.76/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.76/1.51    inference(nnf_transformation,[],[f20])).
% 7.76/1.51  
% 7.76/1.51  fof(f41,plain,(
% 7.76/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.76/1.51    inference(rectify,[],[f40])).
% 7.76/1.51  
% 7.76/1.51  fof(f42,plain,(
% 7.76/1.51    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.76/1.51    introduced(choice_axiom,[])).
% 7.76/1.51  
% 7.76/1.51  fof(f43,plain,(
% 7.76/1.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.76/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 7.76/1.51  
% 7.76/1.51  fof(f68,plain,(
% 7.76/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.76/1.51    inference(cnf_transformation,[],[f43])).
% 7.76/1.51  
% 7.76/1.51  fof(f96,plain,(
% 7.76/1.51    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.76/1.51    inference(equality_resolution,[],[f68])).
% 7.76/1.51  
% 7.76/1.51  fof(f22,axiom,(
% 7.76/1.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f31,plain,(
% 7.76/1.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.76/1.51    inference(ennf_transformation,[],[f22])).
% 7.76/1.51  
% 7.76/1.51  fof(f44,plain,(
% 7.76/1.51    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.76/1.51    inference(nnf_transformation,[],[f31])).
% 7.76/1.51  
% 7.76/1.51  fof(f73,plain,(
% 7.76/1.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f44])).
% 7.76/1.51  
% 7.76/1.51  fof(f3,axiom,(
% 7.76/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f36,plain,(
% 7.76/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.76/1.51    inference(nnf_transformation,[],[f3])).
% 7.76/1.51  
% 7.76/1.51  fof(f37,plain,(
% 7.76/1.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.76/1.51    inference(rectify,[],[f36])).
% 7.76/1.51  
% 7.76/1.51  fof(f38,plain,(
% 7.76/1.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.76/1.51    introduced(choice_axiom,[])).
% 7.76/1.51  
% 7.76/1.51  fof(f39,plain,(
% 7.76/1.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.76/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 7.76/1.51  
% 7.76/1.51  fof(f49,plain,(
% 7.76/1.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f39])).
% 7.76/1.51  
% 7.76/1.51  fof(f27,conjecture,(
% 7.76/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f28,negated_conjecture,(
% 7.76/1.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.76/1.51    inference(negated_conjecture,[],[f27])).
% 7.76/1.51  
% 7.76/1.51  fof(f35,plain,(
% 7.76/1.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.76/1.51    inference(ennf_transformation,[],[f28])).
% 7.76/1.51  
% 7.76/1.51  fof(f45,plain,(
% 7.76/1.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 7.76/1.51    introduced(choice_axiom,[])).
% 7.76/1.51  
% 7.76/1.51  fof(f46,plain,(
% 7.76/1.51    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 7.76/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f45])).
% 7.76/1.51  
% 7.76/1.51  fof(f80,plain,(
% 7.76/1.51    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 7.76/1.51    inference(cnf_transformation,[],[f46])).
% 7.76/1.51  
% 7.76/1.51  fof(f26,axiom,(
% 7.76/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f33,plain,(
% 7.76/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.76/1.51    inference(ennf_transformation,[],[f26])).
% 7.76/1.51  
% 7.76/1.51  fof(f34,plain,(
% 7.76/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.76/1.51    inference(flattening,[],[f33])).
% 7.76/1.51  
% 7.76/1.51  fof(f79,plain,(
% 7.76/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.51    inference(cnf_transformation,[],[f34])).
% 7.76/1.51  
% 7.76/1.51  fof(f13,axiom,(
% 7.76/1.51    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f60,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f13])).
% 7.76/1.51  
% 7.76/1.51  fof(f82,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 7.76/1.51    inference(definition_unfolding,[],[f60,f57])).
% 7.76/1.51  
% 7.76/1.51  fof(f95,plain,(
% 7.76/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.51    inference(definition_unfolding,[],[f79,f82])).
% 7.76/1.51  
% 7.76/1.51  fof(f72,plain,(
% 7.76/1.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f44])).
% 7.76/1.51  
% 7.76/1.51  fof(f25,axiom,(
% 7.76/1.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f78,plain,(
% 7.76/1.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.76/1.51    inference(cnf_transformation,[],[f25])).
% 7.76/1.51  
% 7.76/1.51  fof(f67,plain,(
% 7.76/1.51    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.76/1.51    inference(cnf_transformation,[],[f43])).
% 7.76/1.51  
% 7.76/1.51  fof(f97,plain,(
% 7.76/1.51    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.76/1.51    inference(equality_resolution,[],[f67])).
% 7.76/1.51  
% 7.76/1.51  fof(f7,axiom,(
% 7.76/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f30,plain,(
% 7.76/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.76/1.51    inference(ennf_transformation,[],[f7])).
% 7.76/1.51  
% 7.76/1.51  fof(f54,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.76/1.51    inference(cnf_transformation,[],[f30])).
% 7.76/1.51  
% 7.76/1.51  fof(f92,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.76/1.51    inference(definition_unfolding,[],[f54,f57])).
% 7.76/1.51  
% 7.76/1.51  fof(f24,axiom,(
% 7.76/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f32,plain,(
% 7.76/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.76/1.51    inference(ennf_transformation,[],[f24])).
% 7.76/1.51  
% 7.76/1.51  fof(f77,plain,(
% 7.76/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.51    inference(cnf_transformation,[],[f32])).
% 7.76/1.51  
% 7.76/1.51  fof(f81,plain,(
% 7.76/1.51    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3))),
% 7.76/1.51    inference(cnf_transformation,[],[f46])).
% 7.76/1.51  
% 7.76/1.51  fof(f23,axiom,(
% 7.76/1.51    ! [X0] : k2_subset_1(X0) = X0),
% 7.76/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.51  
% 7.76/1.51  fof(f76,plain,(
% 7.76/1.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.76/1.51    inference(cnf_transformation,[],[f23])).
% 7.76/1.51  
% 7.76/1.51  cnf(c_0,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.76/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_10,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.76/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_11,plain,
% 7.76/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2,plain,
% 7.76/1.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.76/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1014,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_11,c_2]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2565,plain,
% 7.76/1.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_10,c_1014]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2605,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_0,c_2565]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1143,plain,
% 7.76/1.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_10,c_2]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_8,plain,
% 7.76/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.76/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1364,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1370,plain,
% 7.76/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.76/1.51      inference(light_normalisation,[status(thm)],[c_1364,c_10]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1366,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1368,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.76/1.51      inference(light_normalisation,[status(thm)],[c_1366,c_8]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1371,plain,
% 7.76/1.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_1370,c_1368]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1531,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1371,c_11]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1530,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1371,c_11]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1532,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_1530,c_1143]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2044,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1531,c_1532]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2053,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_2044,c_10]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2155,plain,
% 7.76/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_2053,c_2053]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2278,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_0,c_2155]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2653,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(X0,X1) ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_2605,c_1143,c_2278]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_6,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_9502,plain,
% 7.76/1.51      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_2653,c_6]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_9575,plain,
% 7.76/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_9502,c_2653]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1853,plain,
% 7.76/1.51      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1859,plain,
% 7.76/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 7.76/1.51      inference(light_normalisation,[status(thm)],[c_1853,c_0]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1,plain,
% 7.76/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2036,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_0,c_1532]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_3150,plain,
% 7.76/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_2036,c_0]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1384,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_6054,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_3150,c_1384]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_6060,plain,
% 7.76/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_6054,c_1371]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_6365,plain,
% 7.76/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1,c_6060]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_9576,plain,
% 7.76/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 7.76/1.51      inference(light_normalisation,[status(thm)],[c_9575,c_1859,c_6365]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2151,plain,
% 7.76/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1532,c_2053]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_3115,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1384,c_2151]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_13652,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_9576,c_3115]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_13673,plain,
% 7.76/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.76/1.51      inference(demodulation,
% 7.76/1.51                [status(thm)],
% 7.76/1.51                [c_13652,c_1143,c_1370,c_6060]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_9,plain,
% 7.76/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.76/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_992,plain,
% 7.76/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_14,plain,
% 7.76/1.51      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_989,plain,
% 7.76/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.76/1.51      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_19,plain,
% 7.76/1.51      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.76/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_4,plain,
% 7.76/1.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.76/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_119,plain,
% 7.76/1.51      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 7.76/1.51      inference(global_propositional_subsumption,
% 7.76/1.51                [status(thm)],
% 7.76/1.51                [c_19,c_4]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_120,plain,
% 7.76/1.51      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.76/1.51      inference(renaming,[status(thm)],[c_119]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_980,plain,
% 7.76/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.76/1.51      | r2_hidden(X0,X1) != iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_120]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_9655,plain,
% 7.76/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.76/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_989,c_980]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_26,negated_conjecture,
% 7.76/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_981,plain,
% 7.76/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_24,plain,
% 7.76/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.76/1.51      | k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_subset_1(X1,X0,X2) ),
% 7.76/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_553,plain,
% 7.76/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.76/1.51      | k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_subset_1(X1,X0,X2) ),
% 7.76/1.51      inference(theory_normalisation,[status(thm)],[c_24,c_11,c_2]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_982,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_subset_1(X2,X0,X1)
% 7.76/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.76/1.51      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1766,plain,
% 7.76/1.51      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 7.76/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.76/1.51      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_982,c_1384]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1770,plain,
% 7.76/1.51      ( k5_xboole_0(sK3,k4_xboole_0(X0,sK3)) = k4_subset_1(sK2,sK3,X0)
% 7.76/1.51      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_981,c_1766]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_23964,plain,
% 7.76/1.51      ( k5_xboole_0(sK3,k4_xboole_0(X0,sK3)) = k4_subset_1(sK2,sK3,X0)
% 7.76/1.51      | r1_tarski(X0,sK2) != iProver_top ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_9655,c_1770]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_24867,plain,
% 7.76/1.51      ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = k4_subset_1(sK2,sK3,k4_xboole_0(sK2,X0)) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_992,c_23964]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_24882,plain,
% 7.76/1.51      ( k4_subset_1(sK2,sK3,k4_xboole_0(sK2,sK3)) = k5_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_13673,c_24867]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_20,plain,
% 7.76/1.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.76/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_985,plain,
% 7.76/1.51      ( m1_subset_1(X0,X1) != iProver_top
% 7.76/1.51      | r2_hidden(X0,X1) = iProver_top
% 7.76/1.51      | v1_xboole_0(X1) = iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2448,plain,
% 7.76/1.51      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top
% 7.76/1.51      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_981,c_985]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_23,plain,
% 7.76/1.51      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_31,plain,
% 7.76/1.51      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_33,plain,
% 7.76/1.51      ( v1_xboole_0(k1_zfmisc_1(sK2)) != iProver_top ),
% 7.76/1.51      inference(instantiation,[status(thm)],[c_31]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2804,plain,
% 7.76/1.51      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.76/1.51      inference(global_propositional_subsumption,
% 7.76/1.51                [status(thm)],
% 7.76/1.51                [c_2448,c_33]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_15,plain,
% 7.76/1.51      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_988,plain,
% 7.76/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.76/1.51      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_7872,plain,
% 7.76/1.51      ( r1_tarski(sK3,sK2) = iProver_top ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_2804,c_988]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_7,plain,
% 7.76/1.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.76/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_993,plain,
% 7.76/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.76/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_20485,plain,
% 7.76/1.51      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = sK3 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_7872,c_993]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_3120,plain,
% 7.76/1.51      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1384,c_2053]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_20721,plain,
% 7.76/1.51      ( k5_xboole_0(sK3,k4_xboole_0(sK2,sK3)) = sK2 ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_20485,c_3120]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_25012,plain,
% 7.76/1.51      ( k4_subset_1(sK2,sK3,k4_xboole_0(sK2,sK3)) = sK2 ),
% 7.76/1.51      inference(light_normalisation,[status(thm)],[c_24882,c_20721]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_22,plain,
% 7.76/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.51      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.76/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_984,plain,
% 7.76/1.51      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.76/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_22128,plain,
% 7.76/1.51      ( k3_subset_1(sK2,sK3) = k4_xboole_0(sK2,sK3) ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_981,c_984]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_25,negated_conjecture,
% 7.76/1.51      ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_21,plain,
% 7.76/1.51      ( k2_subset_1(X0) = X0 ),
% 7.76/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_996,plain,
% 7.76/1.51      ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,sK3)) != sK2 ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_25,c_21]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_22133,plain,
% 7.76/1.51      ( k4_subset_1(sK2,sK3,k4_xboole_0(sK2,sK3)) != sK2 ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_22128,c_996]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(contradiction,plain,
% 7.76/1.51      ( $false ),
% 7.76/1.51      inference(minisat,[status(thm)],[c_25012,c_22133]) ).
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.51  
% 7.76/1.51  ------                               Statistics
% 7.76/1.51  
% 7.76/1.51  ------ General
% 7.76/1.51  
% 7.76/1.51  abstr_ref_over_cycles:                  0
% 7.76/1.51  abstr_ref_under_cycles:                 0
% 7.76/1.51  gc_basic_clause_elim:                   0
% 7.76/1.51  forced_gc_time:                         0
% 7.76/1.51  parsing_time:                           0.018
% 7.76/1.51  unif_index_cands_time:                  0.
% 7.76/1.51  unif_index_add_time:                    0.
% 7.76/1.51  orderings_time:                         0.
% 7.76/1.51  out_proof_time:                         0.009
% 7.76/1.51  total_time:                             0.693
% 7.76/1.51  num_of_symbols:                         48
% 7.76/1.51  num_of_terms:                           32635
% 7.76/1.51  
% 7.76/1.51  ------ Preprocessing
% 7.76/1.51  
% 7.76/1.51  num_of_splits:                          0
% 7.76/1.51  num_of_split_atoms:                     0
% 7.76/1.51  num_of_reused_defs:                     0
% 7.76/1.51  num_eq_ax_congr_red:                    24
% 7.76/1.51  num_of_sem_filtered_clauses:            1
% 7.76/1.51  num_of_subtypes:                        0
% 7.76/1.51  monotx_restored_types:                  0
% 7.76/1.51  sat_num_of_epr_types:                   0
% 7.76/1.51  sat_num_of_non_cyclic_types:            0
% 7.76/1.51  sat_guarded_non_collapsed_types:        0
% 7.76/1.51  num_pure_diseq_elim:                    0
% 7.76/1.51  simp_replaced_by:                       0
% 7.76/1.51  res_preprocessed:                       108
% 7.76/1.51  prep_upred:                             0
% 7.76/1.51  prep_unflattend:                        34
% 7.76/1.51  smt_new_axioms:                         0
% 7.76/1.51  pred_elim_cands:                        4
% 7.76/1.51  pred_elim:                              0
% 7.76/1.51  pred_elim_cl:                           0
% 7.76/1.51  pred_elim_cycles:                       2
% 7.76/1.51  merged_defs:                            6
% 7.76/1.51  merged_defs_ncl:                        0
% 7.76/1.51  bin_hyper_res:                          6
% 7.76/1.51  prep_cycles:                            3
% 7.76/1.51  pred_elim_time:                         0.007
% 7.76/1.51  splitting_time:                         0.
% 7.76/1.51  sem_filter_time:                        0.
% 7.76/1.51  monotx_time:                            0.001
% 7.76/1.51  subtype_inf_time:                       0.
% 7.76/1.51  
% 7.76/1.51  ------ Problem properties
% 7.76/1.51  
% 7.76/1.51  clauses:                                27
% 7.76/1.51  conjectures:                            2
% 7.76/1.51  epr:                                    5
% 7.76/1.51  horn:                                   24
% 7.76/1.51  ground:                                 2
% 7.76/1.51  unary:                                  14
% 7.76/1.51  binary:                                 7
% 7.76/1.51  lits:                                   46
% 7.76/1.51  lits_eq:                                16
% 7.76/1.51  fd_pure:                                0
% 7.76/1.51  fd_pseudo:                              0
% 7.76/1.51  fd_cond:                                0
% 7.76/1.51  fd_pseudo_cond:                         2
% 7.76/1.51  ac_symbols:                             1
% 7.76/1.51  
% 7.76/1.51  ------ Propositional Solver
% 7.76/1.51  
% 7.76/1.51  prop_solver_calls:                      28
% 7.76/1.51  prop_fast_solver_calls:                 667
% 7.76/1.51  smt_solver_calls:                       0
% 7.76/1.51  smt_fast_solver_calls:                  0
% 7.76/1.51  prop_num_of_clauses:                    5179
% 7.76/1.51  prop_preprocess_simplified:             7370
% 7.76/1.51  prop_fo_subsumed:                       5
% 7.76/1.51  prop_solver_time:                       0.
% 7.76/1.51  smt_solver_time:                        0.
% 7.76/1.51  smt_fast_solver_time:                   0.
% 7.76/1.51  prop_fast_solver_time:                  0.
% 7.76/1.51  prop_unsat_core_time:                   0.
% 7.76/1.51  
% 7.76/1.51  ------ QBF
% 7.76/1.51  
% 7.76/1.51  qbf_q_res:                              0
% 7.76/1.51  qbf_num_tautologies:                    0
% 7.76/1.51  qbf_prep_cycles:                        0
% 7.76/1.51  
% 7.76/1.51  ------ BMC1
% 7.76/1.51  
% 7.76/1.51  bmc1_current_bound:                     -1
% 7.76/1.51  bmc1_last_solved_bound:                 -1
% 7.76/1.51  bmc1_unsat_core_size:                   -1
% 7.76/1.51  bmc1_unsat_core_parents_size:           -1
% 7.76/1.51  bmc1_merge_next_fun:                    0
% 7.76/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.76/1.51  
% 7.76/1.51  ------ Instantiation
% 7.76/1.51  
% 7.76/1.51  inst_num_of_clauses:                    1508
% 7.76/1.51  inst_num_in_passive:                    159
% 7.76/1.51  inst_num_in_active:                     648
% 7.76/1.51  inst_num_in_unprocessed:                701
% 7.76/1.51  inst_num_of_loops:                      700
% 7.76/1.51  inst_num_of_learning_restarts:          0
% 7.76/1.51  inst_num_moves_active_passive:          47
% 7.76/1.51  inst_lit_activity:                      0
% 7.76/1.51  inst_lit_activity_moves:                0
% 7.76/1.51  inst_num_tautologies:                   0
% 7.76/1.51  inst_num_prop_implied:                  0
% 7.76/1.51  inst_num_existing_simplified:           0
% 7.76/1.51  inst_num_eq_res_simplified:             0
% 7.76/1.51  inst_num_child_elim:                    0
% 7.76/1.51  inst_num_of_dismatching_blockings:      344
% 7.76/1.51  inst_num_of_non_proper_insts:           1896
% 7.76/1.51  inst_num_of_duplicates:                 0
% 7.76/1.51  inst_inst_num_from_inst_to_res:         0
% 7.76/1.51  inst_dismatching_checking_time:         0.
% 7.76/1.51  
% 7.76/1.51  ------ Resolution
% 7.76/1.51  
% 7.76/1.51  res_num_of_clauses:                     0
% 7.76/1.51  res_num_in_passive:                     0
% 7.76/1.51  res_num_in_active:                      0
% 7.76/1.51  res_num_of_loops:                       111
% 7.76/1.51  res_forward_subset_subsumed:            492
% 7.76/1.51  res_backward_subset_subsumed:           0
% 7.76/1.51  res_forward_subsumed:                   1
% 7.76/1.51  res_backward_subsumed:                  0
% 7.76/1.51  res_forward_subsumption_resolution:     1
% 7.76/1.51  res_backward_subsumption_resolution:    0
% 7.76/1.51  res_clause_to_clause_subsumption:       42986
% 7.76/1.51  res_orphan_elimination:                 0
% 7.76/1.51  res_tautology_del:                      177
% 7.76/1.51  res_num_eq_res_simplified:              0
% 7.76/1.51  res_num_sel_changes:                    0
% 7.76/1.51  res_moves_from_active_to_pass:          0
% 7.76/1.51  
% 7.76/1.51  ------ Superposition
% 7.76/1.51  
% 7.76/1.51  sup_time_total:                         0.
% 7.76/1.51  sup_time_generating:                    0.
% 7.76/1.51  sup_time_sim_full:                      0.
% 7.76/1.51  sup_time_sim_immed:                     0.
% 7.76/1.51  
% 7.76/1.51  sup_num_of_clauses:                     1692
% 7.76/1.51  sup_num_in_active:                      133
% 7.76/1.51  sup_num_in_passive:                     1559
% 7.76/1.51  sup_num_of_loops:                       139
% 7.76/1.51  sup_fw_superposition:                   6227
% 7.76/1.51  sup_bw_superposition:                   6740
% 7.76/1.51  sup_immediate_simplified:               4751
% 7.76/1.51  sup_given_eliminated:                   3
% 7.76/1.51  comparisons_done:                       0
% 7.76/1.51  comparisons_avoided:                    0
% 7.76/1.51  
% 7.76/1.51  ------ Simplifications
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  sim_fw_subset_subsumed:                 2
% 7.76/1.51  sim_bw_subset_subsumed:                 0
% 7.76/1.51  sim_fw_subsumed:                        714
% 7.76/1.51  sim_bw_subsumed:                        0
% 7.76/1.51  sim_fw_subsumption_res:                 0
% 7.76/1.51  sim_bw_subsumption_res:                 0
% 7.76/1.51  sim_tautology_del:                      5
% 7.76/1.51  sim_eq_tautology_del:                   1216
% 7.76/1.51  sim_eq_res_simp:                        0
% 7.76/1.51  sim_fw_demodulated:                     3059
% 7.76/1.51  sim_bw_demodulated:                     33
% 7.76/1.51  sim_light_normalised:                   1821
% 7.76/1.51  sim_joinable_taut:                      170
% 7.76/1.51  sim_joinable_simp:                      0
% 7.76/1.51  sim_ac_normalised:                      0
% 7.76/1.51  sim_smt_subsumption:                    0
% 7.76/1.51  
%------------------------------------------------------------------------------
