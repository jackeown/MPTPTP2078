%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:32 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 252 expanded)
%              Number of clauses        :   54 (  90 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  273 ( 870 expanded)
%              Number of equality atoms :   81 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK3) )
        & ( r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | ~ r1_tarski(sK2,X2) )
          & ( r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | r1_tarski(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f39,f38])).

fof(f68,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f54,f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1403,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_520,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_521,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_1509,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_521])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_529,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_530,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1510,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_530])).

cnf(c_1597,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1403,c_1509,c_1510])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1410,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5373,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1597,c_1410])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1413,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1404,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1594,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1404,c_1509,c_1510])).

cnf(c_5584,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1594])).

cnf(c_5806,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5373,c_5584])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1411,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5487,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1411])).

cnf(c_6791,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5806,c_5487])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5377,plain,
    ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1410])).

cnf(c_8158,plain,
    ( r1_tarski(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6791,c_5377])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1416,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9864,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),sK3)) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK3) ),
    inference(superposition,[status(thm)],[c_8158,c_1416])).

cnf(c_13,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1409,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_502,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_503,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_505,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_33])).

cnf(c_1401,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1405,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2554,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1405])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1415,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6760,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2554,c_1415])).

cnf(c_7461,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1409,c_6760])).

cnf(c_8607,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7461,c_1411])).

cnf(c_14534,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_8607,c_1416])).

cnf(c_19353,plain,
    ( k2_xboole_0(sK2,sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_9864,c_14534])).

cnf(c_19360,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19353,c_1409])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19360,c_5584])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n004.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 10:30:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.83/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.83/1.47  
% 7.83/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.83/1.47  
% 7.83/1.47  ------  iProver source info
% 7.83/1.47  
% 7.83/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.83/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.83/1.47  git: non_committed_changes: false
% 7.83/1.47  git: last_make_outside_of_git: false
% 7.83/1.47  
% 7.83/1.47  ------ 
% 7.83/1.47  
% 7.83/1.47  ------ Input Options
% 7.83/1.47  
% 7.83/1.47  --out_options                           all
% 7.83/1.47  --tptp_safe_out                         true
% 7.83/1.47  --problem_path                          ""
% 7.83/1.47  --include_path                          ""
% 7.83/1.47  --clausifier                            res/vclausify_rel
% 7.83/1.47  --clausifier_options                    ""
% 7.83/1.47  --stdin                                 false
% 7.83/1.47  --stats_out                             all
% 7.83/1.47  
% 7.83/1.47  ------ General Options
% 7.83/1.47  
% 7.83/1.47  --fof                                   false
% 7.83/1.47  --time_out_real                         305.
% 7.83/1.47  --time_out_virtual                      -1.
% 7.83/1.47  --symbol_type_check                     false
% 7.83/1.47  --clausify_out                          false
% 7.83/1.47  --sig_cnt_out                           false
% 7.83/1.47  --trig_cnt_out                          false
% 7.83/1.47  --trig_cnt_out_tolerance                1.
% 7.83/1.47  --trig_cnt_out_sk_spl                   false
% 7.83/1.47  --abstr_cl_out                          false
% 7.83/1.47  
% 7.83/1.47  ------ Global Options
% 7.83/1.47  
% 7.83/1.47  --schedule                              default
% 7.83/1.47  --add_important_lit                     false
% 7.83/1.47  --prop_solver_per_cl                    1000
% 7.83/1.47  --min_unsat_core                        false
% 7.83/1.47  --soft_assumptions                      false
% 7.83/1.47  --soft_lemma_size                       3
% 7.83/1.47  --prop_impl_unit_size                   0
% 7.83/1.47  --prop_impl_unit                        []
% 7.83/1.47  --share_sel_clauses                     true
% 7.83/1.47  --reset_solvers                         false
% 7.83/1.47  --bc_imp_inh                            [conj_cone]
% 7.83/1.47  --conj_cone_tolerance                   3.
% 7.83/1.47  --extra_neg_conj                        none
% 7.83/1.47  --large_theory_mode                     true
% 7.83/1.47  --prolific_symb_bound                   200
% 7.83/1.47  --lt_threshold                          2000
% 7.83/1.47  --clause_weak_htbl                      true
% 7.83/1.47  --gc_record_bc_elim                     false
% 7.83/1.47  
% 7.83/1.47  ------ Preprocessing Options
% 7.83/1.47  
% 7.83/1.47  --preprocessing_flag                    true
% 7.83/1.47  --time_out_prep_mult                    0.1
% 7.83/1.47  --splitting_mode                        input
% 7.83/1.47  --splitting_grd                         true
% 7.83/1.47  --splitting_cvd                         false
% 7.83/1.47  --splitting_cvd_svl                     false
% 7.83/1.47  --splitting_nvd                         32
% 7.83/1.47  --sub_typing                            true
% 7.83/1.47  --prep_gs_sim                           true
% 7.83/1.47  --prep_unflatten                        true
% 7.83/1.47  --prep_res_sim                          true
% 7.83/1.47  --prep_upred                            true
% 7.83/1.47  --prep_sem_filter                       exhaustive
% 7.83/1.47  --prep_sem_filter_out                   false
% 7.83/1.47  --pred_elim                             true
% 7.83/1.47  --res_sim_input                         true
% 7.83/1.47  --eq_ax_congr_red                       true
% 7.83/1.47  --pure_diseq_elim                       true
% 7.83/1.47  --brand_transform                       false
% 7.83/1.47  --non_eq_to_eq                          false
% 7.83/1.47  --prep_def_merge                        true
% 7.83/1.47  --prep_def_merge_prop_impl              false
% 7.83/1.47  --prep_def_merge_mbd                    true
% 7.83/1.47  --prep_def_merge_tr_red                 false
% 7.83/1.47  --prep_def_merge_tr_cl                  false
% 7.83/1.47  --smt_preprocessing                     true
% 7.83/1.47  --smt_ac_axioms                         fast
% 7.83/1.47  --preprocessed_out                      false
% 7.83/1.47  --preprocessed_stats                    false
% 7.83/1.47  
% 7.83/1.47  ------ Abstraction refinement Options
% 7.83/1.47  
% 7.83/1.47  --abstr_ref                             []
% 7.83/1.47  --abstr_ref_prep                        false
% 7.83/1.47  --abstr_ref_until_sat                   false
% 7.83/1.47  --abstr_ref_sig_restrict                funpre
% 7.83/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.47  --abstr_ref_under                       []
% 7.83/1.47  
% 7.83/1.47  ------ SAT Options
% 7.83/1.47  
% 7.83/1.47  --sat_mode                              false
% 7.83/1.47  --sat_fm_restart_options                ""
% 7.83/1.47  --sat_gr_def                            false
% 7.83/1.47  --sat_epr_types                         true
% 7.83/1.47  --sat_non_cyclic_types                  false
% 7.83/1.47  --sat_finite_models                     false
% 7.83/1.47  --sat_fm_lemmas                         false
% 7.83/1.47  --sat_fm_prep                           false
% 7.83/1.47  --sat_fm_uc_incr                        true
% 7.83/1.47  --sat_out_model                         small
% 7.83/1.47  --sat_out_clauses                       false
% 7.83/1.47  
% 7.83/1.47  ------ QBF Options
% 7.83/1.47  
% 7.83/1.47  --qbf_mode                              false
% 7.83/1.47  --qbf_elim_univ                         false
% 7.83/1.47  --qbf_dom_inst                          none
% 7.83/1.47  --qbf_dom_pre_inst                      false
% 7.83/1.47  --qbf_sk_in                             false
% 7.83/1.47  --qbf_pred_elim                         true
% 7.83/1.47  --qbf_split                             512
% 7.83/1.47  
% 7.83/1.47  ------ BMC1 Options
% 7.83/1.47  
% 7.83/1.47  --bmc1_incremental                      false
% 7.83/1.47  --bmc1_axioms                           reachable_all
% 7.83/1.47  --bmc1_min_bound                        0
% 7.83/1.47  --bmc1_max_bound                        -1
% 7.83/1.47  --bmc1_max_bound_default                -1
% 7.83/1.47  --bmc1_symbol_reachability              true
% 7.83/1.47  --bmc1_property_lemmas                  false
% 7.83/1.47  --bmc1_k_induction                      false
% 7.83/1.47  --bmc1_non_equiv_states                 false
% 7.83/1.47  --bmc1_deadlock                         false
% 7.83/1.47  --bmc1_ucm                              false
% 7.83/1.47  --bmc1_add_unsat_core                   none
% 7.83/1.47  --bmc1_unsat_core_children              false
% 7.83/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.47  --bmc1_out_stat                         full
% 7.83/1.47  --bmc1_ground_init                      false
% 7.83/1.47  --bmc1_pre_inst_next_state              false
% 7.83/1.47  --bmc1_pre_inst_state                   false
% 7.83/1.47  --bmc1_pre_inst_reach_state             false
% 7.83/1.47  --bmc1_out_unsat_core                   false
% 7.83/1.47  --bmc1_aig_witness_out                  false
% 7.83/1.47  --bmc1_verbose                          false
% 7.83/1.47  --bmc1_dump_clauses_tptp                false
% 7.83/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.47  --bmc1_dump_file                        -
% 7.83/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.47  --bmc1_ucm_extend_mode                  1
% 7.83/1.47  --bmc1_ucm_init_mode                    2
% 7.83/1.47  --bmc1_ucm_cone_mode                    none
% 7.83/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.47  --bmc1_ucm_relax_model                  4
% 7.83/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.47  --bmc1_ucm_layered_model                none
% 7.83/1.47  --bmc1_ucm_max_lemma_size               10
% 7.83/1.47  
% 7.83/1.47  ------ AIG Options
% 7.83/1.47  
% 7.83/1.47  --aig_mode                              false
% 7.83/1.47  
% 7.83/1.47  ------ Instantiation Options
% 7.83/1.47  
% 7.83/1.47  --instantiation_flag                    true
% 7.83/1.47  --inst_sos_flag                         true
% 7.83/1.47  --inst_sos_phase                        true
% 7.83/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.47  --inst_lit_sel_side                     num_symb
% 7.83/1.47  --inst_solver_per_active                1400
% 7.83/1.47  --inst_solver_calls_frac                1.
% 7.83/1.47  --inst_passive_queue_type               priority_queues
% 7.83/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.47  --inst_passive_queues_freq              [25;2]
% 7.83/1.47  --inst_dismatching                      true
% 7.83/1.47  --inst_eager_unprocessed_to_passive     true
% 7.83/1.47  --inst_prop_sim_given                   true
% 7.83/1.47  --inst_prop_sim_new                     false
% 7.83/1.47  --inst_subs_new                         false
% 7.83/1.47  --inst_eq_res_simp                      false
% 7.83/1.47  --inst_subs_given                       false
% 7.83/1.47  --inst_orphan_elimination               true
% 7.83/1.47  --inst_learning_loop_flag               true
% 7.83/1.47  --inst_learning_start                   3000
% 7.83/1.47  --inst_learning_factor                  2
% 7.83/1.47  --inst_start_prop_sim_after_learn       3
% 7.83/1.47  --inst_sel_renew                        solver
% 7.83/1.47  --inst_lit_activity_flag                true
% 7.83/1.47  --inst_restr_to_given                   false
% 7.83/1.47  --inst_activity_threshold               500
% 7.83/1.47  --inst_out_proof                        true
% 7.83/1.47  
% 7.83/1.47  ------ Resolution Options
% 7.83/1.47  
% 7.83/1.47  --resolution_flag                       true
% 7.83/1.47  --res_lit_sel                           adaptive
% 7.83/1.47  --res_lit_sel_side                      none
% 7.83/1.47  --res_ordering                          kbo
% 7.83/1.47  --res_to_prop_solver                    active
% 7.83/1.47  --res_prop_simpl_new                    false
% 7.83/1.47  --res_prop_simpl_given                  true
% 7.83/1.47  --res_passive_queue_type                priority_queues
% 7.83/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.47  --res_passive_queues_freq               [15;5]
% 7.83/1.47  --res_forward_subs                      full
% 7.83/1.47  --res_backward_subs                     full
% 7.83/1.47  --res_forward_subs_resolution           true
% 7.83/1.47  --res_backward_subs_resolution          true
% 7.83/1.47  --res_orphan_elimination                true
% 7.83/1.47  --res_time_limit                        2.
% 7.83/1.47  --res_out_proof                         true
% 7.83/1.47  
% 7.83/1.47  ------ Superposition Options
% 7.83/1.47  
% 7.83/1.47  --superposition_flag                    true
% 7.83/1.47  --sup_passive_queue_type                priority_queues
% 7.83/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.47  --demod_completeness_check              fast
% 7.83/1.47  --demod_use_ground                      true
% 7.83/1.47  --sup_to_prop_solver                    passive
% 7.83/1.47  --sup_prop_simpl_new                    true
% 7.83/1.47  --sup_prop_simpl_given                  true
% 7.83/1.47  --sup_fun_splitting                     true
% 7.83/1.47  --sup_smt_interval                      50000
% 7.83/1.47  
% 7.83/1.47  ------ Superposition Simplification Setup
% 7.83/1.47  
% 7.83/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.47  --sup_immed_triv                        [TrivRules]
% 7.83/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.47  --sup_immed_bw_main                     []
% 7.83/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.47  --sup_input_bw                          []
% 7.83/1.47  
% 7.83/1.47  ------ Combination Options
% 7.83/1.47  
% 7.83/1.47  --comb_res_mult                         3
% 7.83/1.47  --comb_sup_mult                         2
% 7.83/1.47  --comb_inst_mult                        10
% 7.83/1.47  
% 7.83/1.47  ------ Debug Options
% 7.83/1.47  
% 7.83/1.47  --dbg_backtrace                         false
% 7.83/1.47  --dbg_dump_prop_clauses                 false
% 7.83/1.47  --dbg_dump_prop_clauses_file            -
% 7.83/1.47  --dbg_out_stat                          false
% 7.83/1.47  ------ Parsing...
% 7.83/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.83/1.47  
% 7.83/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.83/1.47  
% 7.83/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.83/1.47  
% 7.83/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.47  ------ Proving...
% 7.83/1.47  ------ Problem Properties 
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  clauses                                 24
% 7.83/1.47  conjectures                             2
% 7.83/1.47  EPR                                     4
% 7.83/1.47  Horn                                    22
% 7.83/1.47  unary                                   9
% 7.83/1.47  binary                                  11
% 7.83/1.47  lits                                    43
% 7.83/1.47  lits eq                                 12
% 7.83/1.47  fd_pure                                 0
% 7.83/1.47  fd_pseudo                               0
% 7.83/1.47  fd_cond                                 0
% 7.83/1.47  fd_pseudo_cond                          3
% 7.83/1.47  AC symbols                              0
% 7.83/1.47  
% 7.83/1.47  ------ Schedule dynamic 5 is on 
% 7.83/1.47  
% 7.83/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  ------ 
% 7.83/1.47  Current options:
% 7.83/1.47  ------ 
% 7.83/1.47  
% 7.83/1.47  ------ Input Options
% 7.83/1.47  
% 7.83/1.47  --out_options                           all
% 7.83/1.47  --tptp_safe_out                         true
% 7.83/1.47  --problem_path                          ""
% 7.83/1.47  --include_path                          ""
% 7.83/1.47  --clausifier                            res/vclausify_rel
% 7.83/1.47  --clausifier_options                    ""
% 7.83/1.47  --stdin                                 false
% 7.83/1.47  --stats_out                             all
% 7.83/1.47  
% 7.83/1.47  ------ General Options
% 7.83/1.47  
% 7.83/1.47  --fof                                   false
% 7.83/1.47  --time_out_real                         305.
% 7.83/1.47  --time_out_virtual                      -1.
% 7.83/1.47  --symbol_type_check                     false
% 7.83/1.47  --clausify_out                          false
% 7.83/1.47  --sig_cnt_out                           false
% 7.83/1.47  --trig_cnt_out                          false
% 7.83/1.47  --trig_cnt_out_tolerance                1.
% 7.83/1.47  --trig_cnt_out_sk_spl                   false
% 7.83/1.47  --abstr_cl_out                          false
% 7.83/1.47  
% 7.83/1.47  ------ Global Options
% 7.83/1.47  
% 7.83/1.47  --schedule                              default
% 7.83/1.47  --add_important_lit                     false
% 7.83/1.47  --prop_solver_per_cl                    1000
% 7.83/1.47  --min_unsat_core                        false
% 7.83/1.47  --soft_assumptions                      false
% 7.83/1.47  --soft_lemma_size                       3
% 7.83/1.47  --prop_impl_unit_size                   0
% 7.83/1.47  --prop_impl_unit                        []
% 7.83/1.47  --share_sel_clauses                     true
% 7.83/1.47  --reset_solvers                         false
% 7.83/1.47  --bc_imp_inh                            [conj_cone]
% 7.83/1.47  --conj_cone_tolerance                   3.
% 7.83/1.47  --extra_neg_conj                        none
% 7.83/1.47  --large_theory_mode                     true
% 7.83/1.47  --prolific_symb_bound                   200
% 7.83/1.47  --lt_threshold                          2000
% 7.83/1.47  --clause_weak_htbl                      true
% 7.83/1.47  --gc_record_bc_elim                     false
% 7.83/1.47  
% 7.83/1.47  ------ Preprocessing Options
% 7.83/1.47  
% 7.83/1.47  --preprocessing_flag                    true
% 7.83/1.47  --time_out_prep_mult                    0.1
% 7.83/1.47  --splitting_mode                        input
% 7.83/1.47  --splitting_grd                         true
% 7.83/1.47  --splitting_cvd                         false
% 7.83/1.47  --splitting_cvd_svl                     false
% 7.83/1.47  --splitting_nvd                         32
% 7.83/1.47  --sub_typing                            true
% 7.83/1.47  --prep_gs_sim                           true
% 7.83/1.47  --prep_unflatten                        true
% 7.83/1.47  --prep_res_sim                          true
% 7.83/1.47  --prep_upred                            true
% 7.83/1.47  --prep_sem_filter                       exhaustive
% 7.83/1.47  --prep_sem_filter_out                   false
% 7.83/1.47  --pred_elim                             true
% 7.83/1.47  --res_sim_input                         true
% 7.83/1.47  --eq_ax_congr_red                       true
% 7.83/1.47  --pure_diseq_elim                       true
% 7.83/1.47  --brand_transform                       false
% 7.83/1.47  --non_eq_to_eq                          false
% 7.83/1.47  --prep_def_merge                        true
% 7.83/1.47  --prep_def_merge_prop_impl              false
% 7.83/1.47  --prep_def_merge_mbd                    true
% 7.83/1.47  --prep_def_merge_tr_red                 false
% 7.83/1.47  --prep_def_merge_tr_cl                  false
% 7.83/1.47  --smt_preprocessing                     true
% 7.83/1.47  --smt_ac_axioms                         fast
% 7.83/1.47  --preprocessed_out                      false
% 7.83/1.47  --preprocessed_stats                    false
% 7.83/1.47  
% 7.83/1.47  ------ Abstraction refinement Options
% 7.83/1.47  
% 7.83/1.47  --abstr_ref                             []
% 7.83/1.47  --abstr_ref_prep                        false
% 7.83/1.47  --abstr_ref_until_sat                   false
% 7.83/1.47  --abstr_ref_sig_restrict                funpre
% 7.83/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.47  --abstr_ref_under                       []
% 7.83/1.47  
% 7.83/1.47  ------ SAT Options
% 7.83/1.47  
% 7.83/1.47  --sat_mode                              false
% 7.83/1.47  --sat_fm_restart_options                ""
% 7.83/1.47  --sat_gr_def                            false
% 7.83/1.47  --sat_epr_types                         true
% 7.83/1.47  --sat_non_cyclic_types                  false
% 7.83/1.47  --sat_finite_models                     false
% 7.83/1.47  --sat_fm_lemmas                         false
% 7.83/1.47  --sat_fm_prep                           false
% 7.83/1.47  --sat_fm_uc_incr                        true
% 7.83/1.47  --sat_out_model                         small
% 7.83/1.47  --sat_out_clauses                       false
% 7.83/1.47  
% 7.83/1.47  ------ QBF Options
% 7.83/1.47  
% 7.83/1.47  --qbf_mode                              false
% 7.83/1.47  --qbf_elim_univ                         false
% 7.83/1.47  --qbf_dom_inst                          none
% 7.83/1.47  --qbf_dom_pre_inst                      false
% 7.83/1.47  --qbf_sk_in                             false
% 7.83/1.47  --qbf_pred_elim                         true
% 7.83/1.47  --qbf_split                             512
% 7.83/1.47  
% 7.83/1.47  ------ BMC1 Options
% 7.83/1.47  
% 7.83/1.47  --bmc1_incremental                      false
% 7.83/1.47  --bmc1_axioms                           reachable_all
% 7.83/1.47  --bmc1_min_bound                        0
% 7.83/1.47  --bmc1_max_bound                        -1
% 7.83/1.47  --bmc1_max_bound_default                -1
% 7.83/1.47  --bmc1_symbol_reachability              true
% 7.83/1.47  --bmc1_property_lemmas                  false
% 7.83/1.47  --bmc1_k_induction                      false
% 7.83/1.47  --bmc1_non_equiv_states                 false
% 7.83/1.47  --bmc1_deadlock                         false
% 7.83/1.47  --bmc1_ucm                              false
% 7.83/1.47  --bmc1_add_unsat_core                   none
% 7.83/1.47  --bmc1_unsat_core_children              false
% 7.83/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.47  --bmc1_out_stat                         full
% 7.83/1.47  --bmc1_ground_init                      false
% 7.83/1.47  --bmc1_pre_inst_next_state              false
% 7.83/1.47  --bmc1_pre_inst_state                   false
% 7.83/1.47  --bmc1_pre_inst_reach_state             false
% 7.83/1.47  --bmc1_out_unsat_core                   false
% 7.83/1.47  --bmc1_aig_witness_out                  false
% 7.83/1.47  --bmc1_verbose                          false
% 7.83/1.47  --bmc1_dump_clauses_tptp                false
% 7.83/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.47  --bmc1_dump_file                        -
% 7.83/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.47  --bmc1_ucm_extend_mode                  1
% 7.83/1.47  --bmc1_ucm_init_mode                    2
% 7.83/1.47  --bmc1_ucm_cone_mode                    none
% 7.83/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.47  --bmc1_ucm_relax_model                  4
% 7.83/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.47  --bmc1_ucm_layered_model                none
% 7.83/1.47  --bmc1_ucm_max_lemma_size               10
% 7.83/1.47  
% 7.83/1.47  ------ AIG Options
% 7.83/1.47  
% 7.83/1.47  --aig_mode                              false
% 7.83/1.47  
% 7.83/1.47  ------ Instantiation Options
% 7.83/1.47  
% 7.83/1.47  --instantiation_flag                    true
% 7.83/1.47  --inst_sos_flag                         true
% 7.83/1.47  --inst_sos_phase                        true
% 7.83/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.47  --inst_lit_sel_side                     none
% 7.83/1.47  --inst_solver_per_active                1400
% 7.83/1.47  --inst_solver_calls_frac                1.
% 7.83/1.47  --inst_passive_queue_type               priority_queues
% 7.83/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.47  --inst_passive_queues_freq              [25;2]
% 7.83/1.47  --inst_dismatching                      true
% 7.83/1.47  --inst_eager_unprocessed_to_passive     true
% 7.83/1.47  --inst_prop_sim_given                   true
% 7.83/1.47  --inst_prop_sim_new                     false
% 7.83/1.47  --inst_subs_new                         false
% 7.83/1.47  --inst_eq_res_simp                      false
% 7.83/1.47  --inst_subs_given                       false
% 7.83/1.47  --inst_orphan_elimination               true
% 7.83/1.47  --inst_learning_loop_flag               true
% 7.83/1.47  --inst_learning_start                   3000
% 7.83/1.47  --inst_learning_factor                  2
% 7.83/1.47  --inst_start_prop_sim_after_learn       3
% 7.83/1.47  --inst_sel_renew                        solver
% 7.83/1.47  --inst_lit_activity_flag                true
% 7.83/1.47  --inst_restr_to_given                   false
% 7.83/1.47  --inst_activity_threshold               500
% 7.83/1.47  --inst_out_proof                        true
% 7.83/1.47  
% 7.83/1.47  ------ Resolution Options
% 7.83/1.47  
% 7.83/1.47  --resolution_flag                       false
% 7.83/1.47  --res_lit_sel                           adaptive
% 7.83/1.47  --res_lit_sel_side                      none
% 7.83/1.47  --res_ordering                          kbo
% 7.83/1.47  --res_to_prop_solver                    active
% 7.83/1.47  --res_prop_simpl_new                    false
% 7.83/1.47  --res_prop_simpl_given                  true
% 7.83/1.47  --res_passive_queue_type                priority_queues
% 7.83/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.47  --res_passive_queues_freq               [15;5]
% 7.83/1.47  --res_forward_subs                      full
% 7.83/1.47  --res_backward_subs                     full
% 7.83/1.47  --res_forward_subs_resolution           true
% 7.83/1.47  --res_backward_subs_resolution          true
% 7.83/1.47  --res_orphan_elimination                true
% 7.83/1.47  --res_time_limit                        2.
% 7.83/1.47  --res_out_proof                         true
% 7.83/1.47  
% 7.83/1.47  ------ Superposition Options
% 7.83/1.47  
% 7.83/1.47  --superposition_flag                    true
% 7.83/1.47  --sup_passive_queue_type                priority_queues
% 7.83/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.47  --demod_completeness_check              fast
% 7.83/1.47  --demod_use_ground                      true
% 7.83/1.47  --sup_to_prop_solver                    passive
% 7.83/1.47  --sup_prop_simpl_new                    true
% 7.83/1.47  --sup_prop_simpl_given                  true
% 7.83/1.47  --sup_fun_splitting                     true
% 7.83/1.47  --sup_smt_interval                      50000
% 7.83/1.47  
% 7.83/1.47  ------ Superposition Simplification Setup
% 7.83/1.47  
% 7.83/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.47  --sup_immed_triv                        [TrivRules]
% 7.83/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.47  --sup_immed_bw_main                     []
% 7.83/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.47  --sup_input_bw                          []
% 7.83/1.47  
% 7.83/1.47  ------ Combination Options
% 7.83/1.47  
% 7.83/1.47  --comb_res_mult                         3
% 7.83/1.47  --comb_sup_mult                         2
% 7.83/1.47  --comb_inst_mult                        10
% 7.83/1.47  
% 7.83/1.47  ------ Debug Options
% 7.83/1.47  
% 7.83/1.47  --dbg_backtrace                         false
% 7.83/1.47  --dbg_dump_prop_clauses                 false
% 7.83/1.47  --dbg_dump_prop_clauses_file            -
% 7.83/1.47  --dbg_out_stat                          false
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  ------ Proving...
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  % SZS status Theorem for theBenchmark.p
% 7.83/1.47  
% 7.83/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.83/1.47  
% 7.83/1.47  fof(f18,conjecture,(
% 7.83/1.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f19,negated_conjecture,(
% 7.83/1.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.83/1.47    inference(negated_conjecture,[],[f18])).
% 7.83/1.47  
% 7.83/1.47  fof(f28,plain,(
% 7.83/1.47    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.83/1.47    inference(ennf_transformation,[],[f19])).
% 7.83/1.47  
% 7.83/1.47  fof(f36,plain,(
% 7.83/1.47    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.83/1.47    inference(nnf_transformation,[],[f28])).
% 7.83/1.47  
% 7.83/1.47  fof(f37,plain,(
% 7.83/1.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.83/1.47    inference(flattening,[],[f36])).
% 7.83/1.47  
% 7.83/1.47  fof(f39,plain,(
% 7.83/1.47    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 7.83/1.47    introduced(choice_axiom,[])).
% 7.83/1.47  
% 7.83/1.47  fof(f38,plain,(
% 7.83/1.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.83/1.47    introduced(choice_axiom,[])).
% 7.83/1.47  
% 7.83/1.47  fof(f40,plain,(
% 7.83/1.47    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.83/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f39,f38])).
% 7.83/1.47  
% 7.83/1.47  fof(f68,plain,(
% 7.83/1.47    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 7.83/1.47    inference(cnf_transformation,[],[f40])).
% 7.83/1.47  
% 7.83/1.47  fof(f16,axiom,(
% 7.83/1.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f27,plain,(
% 7.83/1.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.83/1.47    inference(ennf_transformation,[],[f16])).
% 7.83/1.47  
% 7.83/1.47  fof(f64,plain,(
% 7.83/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.83/1.47    inference(cnf_transformation,[],[f27])).
% 7.83/1.47  
% 7.83/1.47  fof(f67,plain,(
% 7.83/1.47    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.83/1.47    inference(cnf_transformation,[],[f40])).
% 7.83/1.47  
% 7.83/1.47  fof(f66,plain,(
% 7.83/1.47    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.83/1.47    inference(cnf_transformation,[],[f40])).
% 7.83/1.47  
% 7.83/1.47  fof(f11,axiom,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f25,plain,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.83/1.47    inference(ennf_transformation,[],[f11])).
% 7.83/1.47  
% 7.83/1.47  fof(f53,plain,(
% 7.83/1.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.83/1.47    inference(cnf_transformation,[],[f25])).
% 7.83/1.47  
% 7.83/1.47  fof(f8,axiom,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f23,plain,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.83/1.47    inference(ennf_transformation,[],[f8])).
% 7.83/1.47  
% 7.83/1.47  fof(f50,plain,(
% 7.83/1.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 7.83/1.47    inference(cnf_transformation,[],[f23])).
% 7.83/1.47  
% 7.83/1.47  fof(f69,plain,(
% 7.83/1.47    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 7.83/1.47    inference(cnf_transformation,[],[f40])).
% 7.83/1.47  
% 7.83/1.47  fof(f1,axiom,(
% 7.83/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f41,plain,(
% 7.83/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.83/1.47    inference(cnf_transformation,[],[f1])).
% 7.83/1.47  
% 7.83/1.47  fof(f10,axiom,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f24,plain,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.83/1.47    inference(ennf_transformation,[],[f10])).
% 7.83/1.47  
% 7.83/1.47  fof(f52,plain,(
% 7.83/1.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.83/1.47    inference(cnf_transformation,[],[f24])).
% 7.83/1.47  
% 7.83/1.47  fof(f2,axiom,(
% 7.83/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f42,plain,(
% 7.83/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.83/1.47    inference(cnf_transformation,[],[f2])).
% 7.83/1.47  
% 7.83/1.47  fof(f12,axiom,(
% 7.83/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f54,plain,(
% 7.83/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.83/1.47    inference(cnf_transformation,[],[f12])).
% 7.83/1.47  
% 7.83/1.47  fof(f71,plain,(
% 7.83/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.83/1.47    inference(definition_unfolding,[],[f42,f54,f54])).
% 7.83/1.47  
% 7.83/1.47  fof(f5,axiom,(
% 7.83/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f20,plain,(
% 7.83/1.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.83/1.47    inference(ennf_transformation,[],[f5])).
% 7.83/1.47  
% 7.83/1.47  fof(f47,plain,(
% 7.83/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.83/1.47    inference(cnf_transformation,[],[f20])).
% 7.83/1.47  
% 7.83/1.47  fof(f13,axiom,(
% 7.83/1.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f55,plain,(
% 7.83/1.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.83/1.47    inference(cnf_transformation,[],[f13])).
% 7.83/1.47  
% 7.83/1.47  fof(f15,axiom,(
% 7.83/1.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f26,plain,(
% 7.83/1.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.83/1.47    inference(ennf_transformation,[],[f15])).
% 7.83/1.47  
% 7.83/1.47  fof(f35,plain,(
% 7.83/1.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.83/1.47    inference(nnf_transformation,[],[f26])).
% 7.83/1.47  
% 7.83/1.47  fof(f60,plain,(
% 7.83/1.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.83/1.47    inference(cnf_transformation,[],[f35])).
% 7.83/1.47  
% 7.83/1.47  fof(f17,axiom,(
% 7.83/1.47    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f65,plain,(
% 7.83/1.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.83/1.47    inference(cnf_transformation,[],[f17])).
% 7.83/1.47  
% 7.83/1.47  fof(f14,axiom,(
% 7.83/1.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f31,plain,(
% 7.83/1.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.83/1.47    inference(nnf_transformation,[],[f14])).
% 7.83/1.47  
% 7.83/1.47  fof(f32,plain,(
% 7.83/1.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.83/1.47    inference(rectify,[],[f31])).
% 7.83/1.47  
% 7.83/1.47  fof(f33,plain,(
% 7.83/1.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.83/1.47    introduced(choice_axiom,[])).
% 7.83/1.47  
% 7.83/1.47  fof(f34,plain,(
% 7.83/1.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.83/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.83/1.47  
% 7.83/1.47  fof(f56,plain,(
% 7.83/1.47    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.83/1.47    inference(cnf_transformation,[],[f34])).
% 7.83/1.47  
% 7.83/1.47  fof(f75,plain,(
% 7.83/1.47    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.83/1.47    inference(equality_resolution,[],[f56])).
% 7.83/1.47  
% 7.83/1.47  fof(f6,axiom,(
% 7.83/1.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.83/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.47  
% 7.83/1.47  fof(f21,plain,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.83/1.47    inference(ennf_transformation,[],[f6])).
% 7.83/1.47  
% 7.83/1.47  fof(f22,plain,(
% 7.83/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.83/1.47    inference(flattening,[],[f21])).
% 7.83/1.47  
% 7.83/1.47  fof(f48,plain,(
% 7.83/1.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.83/1.47    inference(cnf_transformation,[],[f22])).
% 7.83/1.47  
% 7.83/1.47  cnf(c_25,negated_conjecture,
% 7.83/1.47      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.83/1.47      | r1_tarski(sK2,sK3) ),
% 7.83/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1403,plain,
% 7.83/1.47      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.83/1.47      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_22,plain,
% 7.83/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.83/1.47      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.83/1.47      inference(cnf_transformation,[],[f64]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_26,negated_conjecture,
% 7.83/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.83/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_520,plain,
% 7.83/1.47      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.83/1.47      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.83/1.47      | sK3 != X1 ),
% 7.83/1.47      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_521,plain,
% 7.83/1.47      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 7.83/1.47      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.83/1.47      inference(unflattening,[status(thm)],[c_520]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1509,plain,
% 7.83/1.47      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 7.83/1.47      inference(equality_resolution,[status(thm)],[c_521]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_27,negated_conjecture,
% 7.83/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.83/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_529,plain,
% 7.83/1.47      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.83/1.47      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.83/1.47      | sK2 != X1 ),
% 7.83/1.47      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_530,plain,
% 7.83/1.47      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 7.83/1.47      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.83/1.47      inference(unflattening,[status(thm)],[c_529]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1510,plain,
% 7.83/1.47      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 7.83/1.47      inference(equality_resolution,[status(thm)],[c_530]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1597,plain,
% 7.83/1.47      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 7.83/1.47      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.83/1.47      inference(light_normalisation,[status(thm)],[c_1403,c_1509,c_1510]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_12,plain,
% 7.83/1.47      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.83/1.47      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.83/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1410,plain,
% 7.83/1.47      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 7.83/1.47      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_5373,plain,
% 7.83/1.47      ( r1_tarski(sK2,sK3) = iProver_top
% 7.83/1.47      | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_1597,c_1410]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_9,plain,
% 7.83/1.47      ( ~ r1_tarski(X0,X1)
% 7.83/1.47      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 7.83/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1413,plain,
% 7.83/1.47      ( r1_tarski(X0,X1) != iProver_top
% 7.83/1.47      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_24,negated_conjecture,
% 7.83/1.47      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.83/1.47      | ~ r1_tarski(sK2,sK3) ),
% 7.83/1.47      inference(cnf_transformation,[],[f69]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1404,plain,
% 7.83/1.47      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 7.83/1.47      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1594,plain,
% 7.83/1.47      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 7.83/1.47      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.83/1.47      inference(light_normalisation,[status(thm)],[c_1404,c_1509,c_1510]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_5584,plain,
% 7.83/1.47      ( r1_tarski(sK2,sK3) != iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_1413,c_1594]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_5806,plain,
% 7.83/1.47      ( r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 7.83/1.47      inference(global_propositional_subsumption,
% 7.83/1.47                [status(thm)],
% 7.83/1.47                [c_5373,c_5584]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1,plain,
% 7.83/1.47      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.83/1.47      inference(cnf_transformation,[],[f41]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_11,plain,
% 7.83/1.47      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.83/1.47      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.83/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1411,plain,
% 7.83/1.47      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.83/1.47      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_5487,plain,
% 7.83/1.47      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.83/1.47      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_1,c_1411]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_6791,plain,
% 7.83/1.47      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_5806,c_5487]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_2,plain,
% 7.83/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.83/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_5377,plain,
% 7.83/1.47      ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = iProver_top
% 7.83/1.47      | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) != iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_2,c_1410]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_8158,plain,
% 7.83/1.47      ( r1_tarski(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),sK3)) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_6791,c_5377]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_6,plain,
% 7.83/1.47      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.83/1.47      inference(cnf_transformation,[],[f47]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1416,plain,
% 7.83/1.47      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_9864,plain,
% 7.83/1.47      ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),sK3)) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK3) ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_8158,c_1416]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_13,plain,
% 7.83/1.47      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.83/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1409,plain,
% 7.83/1.47      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_21,plain,
% 7.83/1.47      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.83/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_502,plain,
% 7.83/1.47      ( r2_hidden(X0,X1)
% 7.83/1.47      | v1_xboole_0(X1)
% 7.83/1.47      | k1_zfmisc_1(sK1) != X1
% 7.83/1.47      | sK2 != X0 ),
% 7.83/1.47      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_503,plain,
% 7.83/1.47      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.83/1.47      inference(unflattening,[status(thm)],[c_502]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_23,plain,
% 7.83/1.47      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.83/1.47      inference(cnf_transformation,[],[f65]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_33,plain,
% 7.83/1.47      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.83/1.47      inference(instantiation,[status(thm)],[c_23]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_505,plain,
% 7.83/1.47      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 7.83/1.47      inference(global_propositional_subsumption,
% 7.83/1.47                [status(thm)],
% 7.83/1.47                [c_503,c_33]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1401,plain,
% 7.83/1.47      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_17,plain,
% 7.83/1.47      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.83/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1405,plain,
% 7.83/1.47      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.83/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_2554,plain,
% 7.83/1.47      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_1401,c_1405]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_7,plain,
% 7.83/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.83/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_1415,plain,
% 7.83/1.47      ( r1_tarski(X0,X1) != iProver_top
% 7.83/1.47      | r1_tarski(X1,X2) != iProver_top
% 7.83/1.47      | r1_tarski(X0,X2) = iProver_top ),
% 7.83/1.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_6760,plain,
% 7.83/1.47      ( r1_tarski(sK2,X0) = iProver_top
% 7.83/1.47      | r1_tarski(sK1,X0) != iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_2554,c_1415]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_7461,plain,
% 7.83/1.47      ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_1409,c_6760]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_8607,plain,
% 7.83/1.47      ( r1_tarski(k4_xboole_0(sK2,sK1),X0) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_7461,c_1411]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_14534,plain,
% 7.83/1.47      ( k2_xboole_0(k4_xboole_0(sK2,sK1),X0) = X0 ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_8607,c_1416]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_19353,plain,
% 7.83/1.47      ( k2_xboole_0(sK2,sK3) = sK3 ),
% 7.83/1.47      inference(demodulation,[status(thm)],[c_9864,c_14534]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(c_19360,plain,
% 7.83/1.47      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.83/1.47      inference(superposition,[status(thm)],[c_19353,c_1409]) ).
% 7.83/1.47  
% 7.83/1.47  cnf(contradiction,plain,
% 7.83/1.47      ( $false ),
% 7.83/1.47      inference(minisat,[status(thm)],[c_19360,c_5584]) ).
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.83/1.47  
% 7.83/1.47  ------                               Statistics
% 7.83/1.47  
% 7.83/1.47  ------ General
% 7.83/1.47  
% 7.83/1.47  abstr_ref_over_cycles:                  0
% 7.83/1.47  abstr_ref_under_cycles:                 0
% 7.83/1.47  gc_basic_clause_elim:                   0
% 7.83/1.47  forced_gc_time:                         0
% 7.83/1.47  parsing_time:                           0.008
% 7.83/1.47  unif_index_cands_time:                  0.
% 7.83/1.47  unif_index_add_time:                    0.
% 7.83/1.47  orderings_time:                         0.
% 7.83/1.47  out_proof_time:                         0.014
% 7.83/1.47  total_time:                             0.746
% 7.83/1.47  num_of_symbols:                         45
% 7.83/1.47  num_of_terms:                           20523
% 7.83/1.47  
% 7.83/1.47  ------ Preprocessing
% 7.83/1.47  
% 7.83/1.47  num_of_splits:                          0
% 7.83/1.47  num_of_split_atoms:                     0
% 7.83/1.47  num_of_reused_defs:                     0
% 7.83/1.47  num_eq_ax_congr_red:                    18
% 7.83/1.47  num_of_sem_filtered_clauses:            1
% 7.83/1.47  num_of_subtypes:                        0
% 7.83/1.47  monotx_restored_types:                  0
% 7.83/1.47  sat_num_of_epr_types:                   0
% 7.83/1.47  sat_num_of_non_cyclic_types:            0
% 7.83/1.47  sat_guarded_non_collapsed_types:        0
% 7.83/1.47  num_pure_diseq_elim:                    0
% 7.83/1.47  simp_replaced_by:                       0
% 7.83/1.47  res_preprocessed:                       116
% 7.83/1.47  prep_upred:                             0
% 7.83/1.47  prep_unflattend:                        46
% 7.83/1.47  smt_new_axioms:                         0
% 7.83/1.47  pred_elim_cands:                        2
% 7.83/1.47  pred_elim:                              2
% 7.83/1.47  pred_elim_cl:                           3
% 7.83/1.47  pred_elim_cycles:                       5
% 7.83/1.47  merged_defs:                            24
% 7.83/1.47  merged_defs_ncl:                        0
% 7.83/1.47  bin_hyper_res:                          25
% 7.83/1.47  prep_cycles:                            4
% 7.83/1.47  pred_elim_time:                         0.007
% 7.83/1.47  splitting_time:                         0.
% 7.83/1.47  sem_filter_time:                        0.
% 7.83/1.47  monotx_time:                            0.
% 7.83/1.47  subtype_inf_time:                       0.
% 7.83/1.47  
% 7.83/1.47  ------ Problem properties
% 7.83/1.47  
% 7.83/1.47  clauses:                                24
% 7.83/1.47  conjectures:                            2
% 7.83/1.47  epr:                                    4
% 7.83/1.47  horn:                                   22
% 7.83/1.47  ground:                                 4
% 7.83/1.47  unary:                                  9
% 7.83/1.47  binary:                                 11
% 7.83/1.47  lits:                                   43
% 7.83/1.47  lits_eq:                                12
% 7.83/1.47  fd_pure:                                0
% 7.83/1.47  fd_pseudo:                              0
% 7.83/1.47  fd_cond:                                0
% 7.83/1.47  fd_pseudo_cond:                         3
% 7.83/1.47  ac_symbols:                             0
% 7.83/1.47  
% 7.83/1.47  ------ Propositional Solver
% 7.83/1.47  
% 7.83/1.47  prop_solver_calls:                      31
% 7.83/1.47  prop_fast_solver_calls:                 787
% 7.83/1.47  smt_solver_calls:                       0
% 7.83/1.47  smt_fast_solver_calls:                  0
% 7.83/1.47  prop_num_of_clauses:                    7646
% 7.83/1.47  prop_preprocess_simplified:             14658
% 7.83/1.47  prop_fo_subsumed:                       9
% 7.83/1.47  prop_solver_time:                       0.
% 7.83/1.47  smt_solver_time:                        0.
% 7.83/1.47  smt_fast_solver_time:                   0.
% 7.83/1.47  prop_fast_solver_time:                  0.
% 7.83/1.47  prop_unsat_core_time:                   0.001
% 7.83/1.47  
% 7.83/1.47  ------ QBF
% 7.83/1.47  
% 7.83/1.47  qbf_q_res:                              0
% 7.83/1.47  qbf_num_tautologies:                    0
% 7.83/1.47  qbf_prep_cycles:                        0
% 7.83/1.47  
% 7.83/1.47  ------ BMC1
% 7.83/1.47  
% 7.83/1.47  bmc1_current_bound:                     -1
% 7.83/1.47  bmc1_last_solved_bound:                 -1
% 7.83/1.47  bmc1_unsat_core_size:                   -1
% 7.83/1.47  bmc1_unsat_core_parents_size:           -1
% 7.83/1.47  bmc1_merge_next_fun:                    0
% 7.83/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.83/1.47  
% 7.83/1.47  ------ Instantiation
% 7.83/1.47  
% 7.83/1.47  inst_num_of_clauses:                    1761
% 7.83/1.47  inst_num_in_passive:                    717
% 7.83/1.47  inst_num_in_active:                     708
% 7.83/1.47  inst_num_in_unprocessed:                337
% 7.83/1.47  inst_num_of_loops:                      920
% 7.83/1.47  inst_num_of_learning_restarts:          0
% 7.83/1.47  inst_num_moves_active_passive:          210
% 7.83/1.47  inst_lit_activity:                      0
% 7.83/1.47  inst_lit_activity_moves:                0
% 7.83/1.47  inst_num_tautologies:                   0
% 7.83/1.47  inst_num_prop_implied:                  0
% 7.83/1.47  inst_num_existing_simplified:           0
% 7.83/1.47  inst_num_eq_res_simplified:             0
% 7.83/1.47  inst_num_child_elim:                    0
% 7.83/1.47  inst_num_of_dismatching_blockings:      1893
% 7.83/1.47  inst_num_of_non_proper_insts:           2816
% 7.83/1.47  inst_num_of_duplicates:                 0
% 7.83/1.47  inst_inst_num_from_inst_to_res:         0
% 7.83/1.47  inst_dismatching_checking_time:         0.
% 7.83/1.47  
% 7.83/1.47  ------ Resolution
% 7.83/1.47  
% 7.83/1.47  res_num_of_clauses:                     0
% 7.83/1.47  res_num_in_passive:                     0
% 7.83/1.47  res_num_in_active:                      0
% 7.83/1.47  res_num_of_loops:                       120
% 7.83/1.47  res_forward_subset_subsumed:            411
% 7.83/1.47  res_backward_subset_subsumed:           12
% 7.83/1.47  res_forward_subsumed:                   3
% 7.83/1.47  res_backward_subsumed:                  0
% 7.83/1.47  res_forward_subsumption_resolution:     2
% 7.83/1.47  res_backward_subsumption_resolution:    0
% 7.83/1.47  res_clause_to_clause_subsumption:       7540
% 7.83/1.47  res_orphan_elimination:                 0
% 7.83/1.47  res_tautology_del:                      219
% 7.83/1.47  res_num_eq_res_simplified:              0
% 7.83/1.47  res_num_sel_changes:                    0
% 7.83/1.47  res_moves_from_active_to_pass:          0
% 7.83/1.47  
% 7.83/1.47  ------ Superposition
% 7.83/1.47  
% 7.83/1.47  sup_time_total:                         0.
% 7.83/1.47  sup_time_generating:                    0.
% 7.83/1.47  sup_time_sim_full:                      0.
% 7.83/1.47  sup_time_sim_immed:                     0.
% 7.83/1.47  
% 7.83/1.47  sup_num_of_clauses:                     780
% 7.83/1.47  sup_num_in_active:                      166
% 7.83/1.47  sup_num_in_passive:                     614
% 7.83/1.47  sup_num_of_loops:                       182
% 7.83/1.47  sup_fw_superposition:                   1024
% 7.83/1.47  sup_bw_superposition:                   1221
% 7.83/1.47  sup_immediate_simplified:               1023
% 7.83/1.47  sup_given_eliminated:                   2
% 7.83/1.47  comparisons_done:                       0
% 7.83/1.47  comparisons_avoided:                    21
% 7.83/1.47  
% 7.83/1.47  ------ Simplifications
% 7.83/1.47  
% 7.83/1.47  
% 7.83/1.47  sim_fw_subset_subsumed:                 0
% 7.83/1.47  sim_bw_subset_subsumed:                 10
% 7.83/1.47  sim_fw_subsumed:                        334
% 7.83/1.47  sim_bw_subsumed:                        6
% 7.83/1.47  sim_fw_subsumption_res:                 0
% 7.83/1.47  sim_bw_subsumption_res:                 0
% 7.83/1.47  sim_tautology_del:                      13
% 7.83/1.47  sim_eq_tautology_del:                   178
% 7.83/1.47  sim_eq_res_simp:                        0
% 7.83/1.47  sim_fw_demodulated:                     471
% 7.83/1.47  sim_bw_demodulated:                     39
% 7.83/1.47  sim_light_normalised:                   513
% 7.83/1.47  sim_joinable_taut:                      0
% 7.83/1.47  sim_joinable_simp:                      0
% 7.83/1.47  sim_ac_normalised:                      0
% 7.83/1.47  sim_smt_subsumption:                    0
% 7.83/1.47  
%------------------------------------------------------------------------------
