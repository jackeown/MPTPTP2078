%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:31 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 182 expanded)
%              Number of clauses        :   49 (  62 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  345 ( 712 expanded)
%              Number of equality atoms :   84 ( 111 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,sK5)))
        & m1_subset_1(sK5,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5)))
    & m1_subset_1(sK5,k1_zfmisc_1(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f35,f34])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ~ r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_920,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_913,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1447,plain,
    ( r2_hidden(sK0(k3_xboole_0(X0,X1),X2),X0) = iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_913])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_921,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5181,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_921])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_912,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5469,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5181,c_912])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_909,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_905,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2320,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_905])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_903,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2320,c_903])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_898,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_902,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1864,plain,
    ( k9_subset_1(sK3,X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_898,c_902])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_900,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_899,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1229,plain,
    ( m1_subset_1(k9_subset_1(sK3,sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k9_subset_1(sK3,sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_899])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1659,plain,
    ( m1_subset_1(k9_subset_1(sK3,sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k9_subset_1(sK3,sK4,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1229,c_26])).

cnf(c_1873,plain,
    ( m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k3_xboole_0(sK4,sK5),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1864,c_1659])).

cnf(c_8013,plain,
    ( r1_tarski(k3_xboole_0(sK4,sK5),sK4) != iProver_top
    | r1_tarski(k3_xboole_0(sK4,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8006,c_1873])).

cnf(c_8563,plain,
    ( r1_tarski(k3_xboole_0(sK4,sK5),sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8013,c_5181])).

cnf(c_8565,plain,
    ( r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5469,c_8563])).

cnf(c_897,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_904,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2304,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_904])).

cnf(c_38,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_40,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_1125,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
    | r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1126,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_2437,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2304,c_26,c_40,c_1126])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_908,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2443,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_908])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8565,c_2443])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.27/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/0.99  
% 3.27/0.99  ------  iProver source info
% 3.27/0.99  
% 3.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/0.99  git: non_committed_changes: false
% 3.27/0.99  git: last_make_outside_of_git: false
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     num_symb
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       true
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  ------ Parsing...
% 3.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/0.99  ------ Proving...
% 3.27/0.99  ------ Problem Properties 
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  clauses                                 26
% 3.27/0.99  conjectures                             3
% 3.27/0.99  EPR                                     6
% 3.27/0.99  Horn                                    20
% 3.27/0.99  unary                                   5
% 3.27/0.99  binary                                  7
% 3.27/0.99  lits                                    64
% 3.27/0.99  lits eq                                 7
% 3.27/0.99  fd_pure                                 0
% 3.27/0.99  fd_pseudo                               0
% 3.27/0.99  fd_cond                                 0
% 3.27/0.99  fd_pseudo_cond                          5
% 3.27/0.99  AC symbols                              0
% 3.27/0.99  
% 3.27/0.99  ------ Schedule dynamic 5 is on 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  Current options:
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     none
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       false
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ Proving...
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS status Theorem for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  fof(f2,axiom,(
% 3.27/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f12,plain,(
% 3.27/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f2])).
% 3.27/0.99  
% 3.27/0.99  fof(f19,plain,(
% 3.27/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/0.99    inference(nnf_transformation,[],[f12])).
% 3.27/0.99  
% 3.27/0.99  fof(f20,plain,(
% 3.27/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/0.99    inference(rectify,[],[f19])).
% 3.27/0.99  
% 3.27/0.99  fof(f21,plain,(
% 3.27/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f22,plain,(
% 3.27/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.27/0.99  
% 3.27/0.99  fof(f39,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f22])).
% 3.27/0.99  
% 3.27/0.99  fof(f3,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f23,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.27/0.99    inference(nnf_transformation,[],[f3])).
% 3.27/0.99  
% 3.27/0.99  fof(f24,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.27/0.99    inference(flattening,[],[f23])).
% 3.27/0.99  
% 3.27/0.99  fof(f25,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.27/0.99    inference(rectify,[],[f24])).
% 3.27/0.99  
% 3.27/0.99  fof(f26,plain,(
% 3.27/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f27,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 3.27/0.99  
% 3.27/0.99  fof(f41,plain,(
% 3.27/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f65,plain,(
% 3.27/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.27/0.99    inference(equality_resolution,[],[f41])).
% 3.27/0.99  
% 3.27/0.99  fof(f40,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f22])).
% 3.27/0.99  
% 3.27/0.99  fof(f4,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f13,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.27/0.99    inference(ennf_transformation,[],[f4])).
% 3.27/0.99  
% 3.27/0.99  fof(f14,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.27/0.99    inference(flattening,[],[f13])).
% 3.27/0.99  
% 3.27/0.99  fof(f47,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f14])).
% 3.27/0.99  
% 3.27/0.99  fof(f5,axiom,(
% 3.27/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f28,plain,(
% 3.27/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.27/0.99    inference(nnf_transformation,[],[f5])).
% 3.27/0.99  
% 3.27/0.99  fof(f29,plain,(
% 3.27/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.27/0.99    inference(rectify,[],[f28])).
% 3.27/0.99  
% 3.27/0.99  fof(f30,plain,(
% 3.27/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f31,plain,(
% 3.27/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.27/0.99  
% 3.27/0.99  fof(f49,plain,(
% 3.27/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.27/0.99    inference(cnf_transformation,[],[f31])).
% 3.27/0.99  
% 3.27/0.99  fof(f66,plain,(
% 3.27/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.27/0.99    inference(equality_resolution,[],[f49])).
% 3.27/0.99  
% 3.27/0.99  fof(f6,axiom,(
% 3.27/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f15,plain,(
% 3.27/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f6])).
% 3.27/0.99  
% 3.27/0.99  fof(f32,plain,(
% 3.27/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.27/0.99    inference(nnf_transformation,[],[f15])).
% 3.27/0.99  
% 3.27/0.99  fof(f53,plain,(
% 3.27/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f32])).
% 3.27/0.99  
% 3.27/0.99  fof(f7,axiom,(
% 3.27/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f56,plain,(
% 3.27/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f7])).
% 3.27/0.99  
% 3.27/0.99  fof(f10,conjecture,(
% 3.27/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f11,negated_conjecture,(
% 3.27/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 3.27/0.99    inference(negated_conjecture,[],[f10])).
% 3.27/0.99  
% 3.27/0.99  fof(f18,plain,(
% 3.27/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f11])).
% 3.27/0.99  
% 3.27/0.99  fof(f35,plain,(
% 3.27/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(X0)))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f34,plain,(
% 3.27/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f36,plain,(
% 3.27/0.99    (~r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5))) & m1_subset_1(sK5,k1_zfmisc_1(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f35,f34])).
% 3.27/0.99  
% 3.27/0.99  fof(f61,plain,(
% 3.27/0.99    m1_subset_1(sK5,k1_zfmisc_1(sK3))),
% 3.27/0.99    inference(cnf_transformation,[],[f36])).
% 3.27/0.99  
% 3.27/0.99  fof(f8,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f16,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f8])).
% 3.27/0.99  
% 3.27/0.99  fof(f57,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f16])).
% 3.27/0.99  
% 3.27/0.99  fof(f9,axiom,(
% 3.27/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f17,plain,(
% 3.27/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f9])).
% 3.27/0.99  
% 3.27/0.99  fof(f33,plain,(
% 3.27/0.99    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.27/0.99    inference(nnf_transformation,[],[f17])).
% 3.27/0.99  
% 3.27/0.99  fof(f58,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f33])).
% 3.27/0.99  
% 3.27/0.99  fof(f62,plain,(
% 3.27/0.99    ~r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5)))),
% 3.27/0.99    inference(cnf_transformation,[],[f36])).
% 3.27/0.99  
% 3.27/0.99  fof(f60,plain,(
% 3.27/0.99    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 3.27/0.99    inference(cnf_transformation,[],[f36])).
% 3.27/0.99  
% 3.27/0.99  fof(f52,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f32])).
% 3.27/0.99  
% 3.27/0.99  fof(f48,plain,(
% 3.27/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.27/0.99    inference(cnf_transformation,[],[f31])).
% 3.27/0.99  
% 3.27/0.99  fof(f67,plain,(
% 3.27/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.27/0.99    inference(equality_resolution,[],[f48])).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_920,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_9,plain,
% 3.27/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_913,plain,
% 3.27/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.27/0.99      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1447,plain,
% 3.27/0.99      ( r2_hidden(sK0(k3_xboole_0(X0,X1),X2),X0) = iProver_top
% 3.27/0.99      | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_920,c_913]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1,plain,
% 3.27/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_921,plain,
% 3.27/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5181,plain,
% 3.27/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1447,c_921]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_10,plain,
% 3.27/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.27/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_912,plain,
% 3.27/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.27/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5469,plain,
% 3.27/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.27/0.99      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_5181,c_912]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_13,plain,
% 3.27/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_909,plain,
% 3.27/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_17,plain,
% 3.27/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_905,plain,
% 3.27/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.27/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.27/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2320,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.27/0.99      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_909,c_905]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_19,plain,
% 3.27/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_903,plain,
% 3.27/0.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8006,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.27/0.99      inference(forward_subsumption_resolution,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_2320,c_903]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_24,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_898,plain,
% 3.27/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_20,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.27/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_902,plain,
% 3.27/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.27/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1864,plain,
% 3.27/0.99      ( k9_subset_1(sK3,X0,sK5) = k3_xboole_0(X0,sK5) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_898,c_902]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_22,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.27/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.27/0.99      | ~ r1_tarski(X2,X0)
% 3.27/0.99      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_900,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.27/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.27/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.27/0.99      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_23,negated_conjecture,
% 3.27/0.99      ( ~ r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5))) ),
% 3.27/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_899,plain,
% 3.27/0.99      ( r1_tarski(k3_subset_1(sK3,sK4),k3_subset_1(sK3,k9_subset_1(sK3,sK4,sK5))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1229,plain,
% 3.27/0.99      ( m1_subset_1(k9_subset_1(sK3,sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top
% 3.27/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
% 3.27/0.99      | r1_tarski(k9_subset_1(sK3,sK4,sK5),sK4) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_900,c_899]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_25,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_26,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1659,plain,
% 3.27/0.99      ( m1_subset_1(k9_subset_1(sK3,sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top
% 3.27/0.99      | r1_tarski(k9_subset_1(sK3,sK4,sK5),sK4) != iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_1229,c_26]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1873,plain,
% 3.27/0.99      ( m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top
% 3.27/0.99      | r1_tarski(k3_xboole_0(sK4,sK5),sK4) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_1864,c_1659]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8013,plain,
% 3.27/0.99      ( r1_tarski(k3_xboole_0(sK4,sK5),sK4) != iProver_top
% 3.27/0.99      | r1_tarski(k3_xboole_0(sK4,sK5),sK3) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_8006,c_1873]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8563,plain,
% 3.27/0.99      ( r1_tarski(k3_xboole_0(sK4,sK5),sK3) != iProver_top ),
% 3.27/0.99      inference(forward_subsumption_resolution,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_8013,c_5181]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8565,plain,
% 3.27/0.99      ( r1_tarski(sK4,sK3) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_5469,c_8563]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_897,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_18,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_904,plain,
% 3.27/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.27/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.27/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2304,plain,
% 3.27/0.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
% 3.27/0.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_897,c_904]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_38,plain,
% 3.27/0.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_40,plain,
% 3.27/0.99      ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_38]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1125,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
% 3.27/0.99      | r2_hidden(sK4,k1_zfmisc_1(sK3))
% 3.27/0.99      | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1126,plain,
% 3.27/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) != iProver_top
% 3.27/0.99      | r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top
% 3.27/0.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2437,plain,
% 3.27/0.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_2304,c_26,c_40,c_1126]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_14,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_908,plain,
% 3.27/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2443,plain,
% 3.27/0.99      ( r1_tarski(sK4,sK3) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2437,c_908]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(contradiction,plain,
% 3.27/0.99      ( $false ),
% 3.27/0.99      inference(minisat,[status(thm)],[c_8565,c_2443]) ).
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  ------                               Statistics
% 3.27/0.99  
% 3.27/0.99  ------ General
% 3.27/0.99  
% 3.27/0.99  abstr_ref_over_cycles:                  0
% 3.27/0.99  abstr_ref_under_cycles:                 0
% 3.27/0.99  gc_basic_clause_elim:                   0
% 3.27/0.99  forced_gc_time:                         0
% 3.27/0.99  parsing_time:                           0.008
% 3.27/0.99  unif_index_cands_time:                  0.
% 3.27/0.99  unif_index_add_time:                    0.
% 3.27/0.99  orderings_time:                         0.
% 3.27/0.99  out_proof_time:                         0.008
% 3.27/0.99  total_time:                             0.232
% 3.27/0.99  num_of_symbols:                         45
% 3.27/0.99  num_of_terms:                           7855
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing
% 3.27/0.99  
% 3.27/0.99  num_of_splits:                          0
% 3.27/0.99  num_of_split_atoms:                     0
% 3.27/0.99  num_of_reused_defs:                     0
% 3.27/0.99  num_eq_ax_congr_red:                    18
% 3.27/0.99  num_of_sem_filtered_clauses:            1
% 3.27/0.99  num_of_subtypes:                        0
% 3.27/0.99  monotx_restored_types:                  0
% 3.27/0.99  sat_num_of_epr_types:                   0
% 3.27/0.99  sat_num_of_non_cyclic_types:            0
% 3.27/0.99  sat_guarded_non_collapsed_types:        0
% 3.27/0.99  num_pure_diseq_elim:                    0
% 3.27/0.99  simp_replaced_by:                       0
% 3.27/0.99  res_preprocessed:                       97
% 3.27/0.99  prep_upred:                             0
% 3.27/0.99  prep_unflattend:                        0
% 3.27/0.99  smt_new_axioms:                         0
% 3.27/0.99  pred_elim_cands:                        4
% 3.27/0.99  pred_elim:                              0
% 3.27/0.99  pred_elim_cl:                           0
% 3.27/0.99  pred_elim_cycles:                       1
% 3.27/0.99  merged_defs:                            6
% 3.27/0.99  merged_defs_ncl:                        0
% 3.27/0.99  bin_hyper_res:                          6
% 3.27/0.99  prep_cycles:                            3
% 3.27/0.99  pred_elim_time:                         0.
% 3.27/0.99  splitting_time:                         0.
% 3.27/0.99  sem_filter_time:                        0.
% 3.27/0.99  monotx_time:                            0.001
% 3.27/0.99  subtype_inf_time:                       0.
% 3.27/0.99  
% 3.27/0.99  ------ Problem properties
% 3.27/0.99  
% 3.27/0.99  clauses:                                26
% 3.27/0.99  conjectures:                            3
% 3.27/0.99  epr:                                    6
% 3.27/0.99  horn:                                   20
% 3.27/0.99  ground:                                 3
% 3.27/0.99  unary:                                  5
% 3.27/0.99  binary:                                 7
% 3.27/0.99  lits:                                   64
% 3.27/0.99  lits_eq:                                7
% 3.27/0.99  fd_pure:                                0
% 3.27/0.99  fd_pseudo:                              0
% 3.27/0.99  fd_cond:                                0
% 3.27/0.99  fd_pseudo_cond:                         5
% 3.27/0.99  ac_symbols:                             0
% 3.27/0.99  
% 3.27/0.99  ------ Propositional Solver
% 3.27/0.99  
% 3.27/0.99  prop_solver_calls:                      24
% 3.27/0.99  prop_fast_solver_calls:                 688
% 3.27/0.99  smt_solver_calls:                       0
% 3.27/0.99  smt_fast_solver_calls:                  0
% 3.27/0.99  prop_num_of_clauses:                    3387
% 3.27/0.99  prop_preprocess_simplified:             7965
% 3.27/0.99  prop_fo_subsumed:                       4
% 3.27/0.99  prop_solver_time:                       0.
% 3.27/0.99  smt_solver_time:                        0.
% 3.27/0.99  smt_fast_solver_time:                   0.
% 3.27/0.99  prop_fast_solver_time:                  0.
% 3.27/0.99  prop_unsat_core_time:                   0.
% 3.27/0.99  
% 3.27/0.99  ------ QBF
% 3.27/0.99  
% 3.27/0.99  qbf_q_res:                              0
% 3.27/0.99  qbf_num_tautologies:                    0
% 3.27/0.99  qbf_prep_cycles:                        0
% 3.27/0.99  
% 3.27/0.99  ------ BMC1
% 3.27/0.99  
% 3.27/0.99  bmc1_current_bound:                     -1
% 3.27/0.99  bmc1_last_solved_bound:                 -1
% 3.27/0.99  bmc1_unsat_core_size:                   -1
% 3.27/0.99  bmc1_unsat_core_parents_size:           -1
% 3.27/0.99  bmc1_merge_next_fun:                    0
% 3.27/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation
% 3.27/0.99  
% 3.27/0.99  inst_num_of_clauses:                    884
% 3.27/0.99  inst_num_in_passive:                    278
% 3.27/0.99  inst_num_in_active:                     358
% 3.27/0.99  inst_num_in_unprocessed:                248
% 3.27/0.99  inst_num_of_loops:                      450
% 3.27/0.99  inst_num_of_learning_restarts:          0
% 3.27/0.99  inst_num_moves_active_passive:          90
% 3.27/0.99  inst_lit_activity:                      0
% 3.27/0.99  inst_lit_activity_moves:                0
% 3.27/0.99  inst_num_tautologies:                   0
% 3.27/0.99  inst_num_prop_implied:                  0
% 3.27/0.99  inst_num_existing_simplified:           0
% 3.27/0.99  inst_num_eq_res_simplified:             0
% 3.27/0.99  inst_num_child_elim:                    0
% 3.27/0.99  inst_num_of_dismatching_blockings:      626
% 3.27/0.99  inst_num_of_non_proper_insts:           963
% 3.27/0.99  inst_num_of_duplicates:                 0
% 3.27/0.99  inst_inst_num_from_inst_to_res:         0
% 3.27/0.99  inst_dismatching_checking_time:         0.
% 3.27/0.99  
% 3.27/0.99  ------ Resolution
% 3.27/0.99  
% 3.27/0.99  res_num_of_clauses:                     0
% 3.27/0.99  res_num_in_passive:                     0
% 3.27/0.99  res_num_in_active:                      0
% 3.27/0.99  res_num_of_loops:                       100
% 3.27/0.99  res_forward_subset_subsumed:            50
% 3.27/0.99  res_backward_subset_subsumed:           0
% 3.27/0.99  res_forward_subsumed:                   0
% 3.27/0.99  res_backward_subsumed:                  0
% 3.27/0.99  res_forward_subsumption_resolution:     0
% 3.27/0.99  res_backward_subsumption_resolution:    0
% 3.27/0.99  res_clause_to_clause_subsumption:       1083
% 3.27/0.99  res_orphan_elimination:                 0
% 3.27/0.99  res_tautology_del:                      51
% 3.27/0.99  res_num_eq_res_simplified:              0
% 3.27/0.99  res_num_sel_changes:                    0
% 3.27/0.99  res_moves_from_active_to_pass:          0
% 3.27/0.99  
% 3.27/0.99  ------ Superposition
% 3.27/0.99  
% 3.27/0.99  sup_time_total:                         0.
% 3.27/0.99  sup_time_generating:                    0.
% 3.27/0.99  sup_time_sim_full:                      0.
% 3.27/0.99  sup_time_sim_immed:                     0.
% 3.27/0.99  
% 3.27/0.99  sup_num_of_clauses:                     187
% 3.27/0.99  sup_num_in_active:                      88
% 3.27/0.99  sup_num_in_passive:                     99
% 3.27/0.99  sup_num_of_loops:                       89
% 3.27/0.99  sup_fw_superposition:                   145
% 3.27/0.99  sup_bw_superposition:                   164
% 3.27/0.99  sup_immediate_simplified:               30
% 3.27/0.99  sup_given_eliminated:                   0
% 3.27/0.99  comparisons_done:                       0
% 3.27/0.99  comparisons_avoided:                    0
% 3.27/0.99  
% 3.27/0.99  ------ Simplifications
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  sim_fw_subset_subsumed:                 16
% 3.27/0.99  sim_bw_subset_subsumed:                 6
% 3.27/0.99  sim_fw_subsumed:                        10
% 3.27/0.99  sim_bw_subsumed:                        0
% 3.27/0.99  sim_fw_subsumption_res:                 2
% 3.27/0.99  sim_bw_subsumption_res:                 0
% 3.27/0.99  sim_tautology_del:                      18
% 3.27/0.99  sim_eq_tautology_del:                   0
% 3.27/0.99  sim_eq_res_simp:                        2
% 3.27/0.99  sim_fw_demodulated:                     0
% 3.27/0.99  sim_bw_demodulated:                     2
% 3.27/0.99  sim_light_normalised:                   0
% 3.27/0.99  sim_joinable_taut:                      0
% 3.27/0.99  sim_joinable_simp:                      0
% 3.27/0.99  sim_ac_normalised:                      0
% 3.27/0.99  sim_smt_subsumption:                    0
% 3.27/0.99  
%------------------------------------------------------------------------------
