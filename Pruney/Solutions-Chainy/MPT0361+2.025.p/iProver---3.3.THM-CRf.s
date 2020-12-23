%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:29 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 166 expanded)
%              Number of clauses        :   36 (  45 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 ( 475 expanded)
%              Number of equality atoms :  154 ( 168 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f33,f32])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f74,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f75,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_738,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_737,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_743,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_742,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1268,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k4_subset_1(X0,X1,X2))) = k4_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_743,c_742])).

cnf(c_3648,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k4_subset_1(sK1,sK2,X0))) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_1268])).

cnf(c_4392,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3))) = k4_subset_1(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_738,c_3648])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(X0,k4_subset_1(sK1,sK2,sK3)) != iProver_top
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4392,c_740])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_782,plain,
    ( ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | m1_subset_1(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_783,plain,
    ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_811,plain,
    ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_812,plain,
    ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_29714,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(X0,k4_subset_1(sK1,sK2,sK3)) != iProver_top
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4401,c_17,c_18,c_783,c_812])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_739,plain,
    ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_29805,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29714,c_739])).

cnf(c_5,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_748,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_741,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1340,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_741])).

cnf(c_1720,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k4_subset_1(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_738,c_1340])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_745,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1728,plain,
    ( r1_tarski(X0,k4_subset_1(sK1,sK2,sK3)) = iProver_top
    | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_745])).

cnf(c_2762,plain,
    ( r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_1728])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29805,c_2762,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:00:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.31/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/1.52  
% 7.31/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.31/1.52  
% 7.31/1.52  ------  iProver source info
% 7.31/1.52  
% 7.31/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.31/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.31/1.52  git: non_committed_changes: false
% 7.31/1.52  git: last_make_outside_of_git: false
% 7.31/1.52  
% 7.31/1.52  ------ 
% 7.31/1.52  
% 7.31/1.52  ------ Input Options
% 7.31/1.52  
% 7.31/1.52  --out_options                           all
% 7.31/1.52  --tptp_safe_out                         true
% 7.31/1.52  --problem_path                          ""
% 7.31/1.52  --include_path                          ""
% 7.31/1.52  --clausifier                            res/vclausify_rel
% 7.31/1.52  --clausifier_options                    ""
% 7.31/1.52  --stdin                                 false
% 7.31/1.52  --stats_out                             all
% 7.31/1.52  
% 7.31/1.52  ------ General Options
% 7.31/1.52  
% 7.31/1.52  --fof                                   false
% 7.31/1.52  --time_out_real                         305.
% 7.31/1.52  --time_out_virtual                      -1.
% 7.31/1.52  --symbol_type_check                     false
% 7.31/1.52  --clausify_out                          false
% 7.31/1.52  --sig_cnt_out                           false
% 7.31/1.52  --trig_cnt_out                          false
% 7.31/1.52  --trig_cnt_out_tolerance                1.
% 7.31/1.52  --trig_cnt_out_sk_spl                   false
% 7.31/1.52  --abstr_cl_out                          false
% 7.31/1.52  
% 7.31/1.52  ------ Global Options
% 7.31/1.52  
% 7.31/1.52  --schedule                              default
% 7.31/1.52  --add_important_lit                     false
% 7.31/1.52  --prop_solver_per_cl                    1000
% 7.31/1.52  --min_unsat_core                        false
% 7.31/1.52  --soft_assumptions                      false
% 7.31/1.52  --soft_lemma_size                       3
% 7.31/1.52  --prop_impl_unit_size                   0
% 7.31/1.52  --prop_impl_unit                        []
% 7.31/1.52  --share_sel_clauses                     true
% 7.31/1.52  --reset_solvers                         false
% 7.31/1.52  --bc_imp_inh                            [conj_cone]
% 7.31/1.52  --conj_cone_tolerance                   3.
% 7.31/1.52  --extra_neg_conj                        none
% 7.31/1.52  --large_theory_mode                     true
% 7.31/1.52  --prolific_symb_bound                   200
% 7.31/1.52  --lt_threshold                          2000
% 7.31/1.52  --clause_weak_htbl                      true
% 7.31/1.52  --gc_record_bc_elim                     false
% 7.31/1.52  
% 7.31/1.52  ------ Preprocessing Options
% 7.31/1.52  
% 7.31/1.52  --preprocessing_flag                    true
% 7.31/1.52  --time_out_prep_mult                    0.1
% 7.31/1.52  --splitting_mode                        input
% 7.31/1.52  --splitting_grd                         true
% 7.31/1.52  --splitting_cvd                         false
% 7.31/1.52  --splitting_cvd_svl                     false
% 7.31/1.52  --splitting_nvd                         32
% 7.31/1.52  --sub_typing                            true
% 7.31/1.52  --prep_gs_sim                           true
% 7.31/1.52  --prep_unflatten                        true
% 7.31/1.52  --prep_res_sim                          true
% 7.31/1.52  --prep_upred                            true
% 7.31/1.52  --prep_sem_filter                       exhaustive
% 7.31/1.52  --prep_sem_filter_out                   false
% 7.31/1.52  --pred_elim                             true
% 7.31/1.52  --res_sim_input                         true
% 7.31/1.52  --eq_ax_congr_red                       true
% 7.31/1.52  --pure_diseq_elim                       true
% 7.31/1.52  --brand_transform                       false
% 7.31/1.52  --non_eq_to_eq                          false
% 7.31/1.52  --prep_def_merge                        true
% 7.31/1.52  --prep_def_merge_prop_impl              false
% 7.31/1.52  --prep_def_merge_mbd                    true
% 7.31/1.52  --prep_def_merge_tr_red                 false
% 7.31/1.52  --prep_def_merge_tr_cl                  false
% 7.31/1.52  --smt_preprocessing                     true
% 7.31/1.52  --smt_ac_axioms                         fast
% 7.31/1.52  --preprocessed_out                      false
% 7.31/1.52  --preprocessed_stats                    false
% 7.31/1.52  
% 7.31/1.52  ------ Abstraction refinement Options
% 7.31/1.52  
% 7.31/1.52  --abstr_ref                             []
% 7.31/1.52  --abstr_ref_prep                        false
% 7.31/1.52  --abstr_ref_until_sat                   false
% 7.31/1.52  --abstr_ref_sig_restrict                funpre
% 7.31/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.31/1.52  --abstr_ref_under                       []
% 7.31/1.52  
% 7.31/1.52  ------ SAT Options
% 7.31/1.52  
% 7.31/1.52  --sat_mode                              false
% 7.31/1.52  --sat_fm_restart_options                ""
% 7.31/1.52  --sat_gr_def                            false
% 7.31/1.52  --sat_epr_types                         true
% 7.31/1.52  --sat_non_cyclic_types                  false
% 7.31/1.52  --sat_finite_models                     false
% 7.31/1.52  --sat_fm_lemmas                         false
% 7.31/1.52  --sat_fm_prep                           false
% 7.31/1.52  --sat_fm_uc_incr                        true
% 7.31/1.52  --sat_out_model                         small
% 7.31/1.52  --sat_out_clauses                       false
% 7.31/1.52  
% 7.31/1.52  ------ QBF Options
% 7.31/1.52  
% 7.31/1.52  --qbf_mode                              false
% 7.31/1.52  --qbf_elim_univ                         false
% 7.31/1.52  --qbf_dom_inst                          none
% 7.31/1.52  --qbf_dom_pre_inst                      false
% 7.31/1.52  --qbf_sk_in                             false
% 7.31/1.52  --qbf_pred_elim                         true
% 7.31/1.52  --qbf_split                             512
% 7.31/1.52  
% 7.31/1.52  ------ BMC1 Options
% 7.31/1.52  
% 7.31/1.52  --bmc1_incremental                      false
% 7.31/1.52  --bmc1_axioms                           reachable_all
% 7.31/1.52  --bmc1_min_bound                        0
% 7.31/1.52  --bmc1_max_bound                        -1
% 7.31/1.52  --bmc1_max_bound_default                -1
% 7.31/1.52  --bmc1_symbol_reachability              true
% 7.31/1.52  --bmc1_property_lemmas                  false
% 7.31/1.52  --bmc1_k_induction                      false
% 7.31/1.52  --bmc1_non_equiv_states                 false
% 7.31/1.52  --bmc1_deadlock                         false
% 7.31/1.52  --bmc1_ucm                              false
% 7.31/1.52  --bmc1_add_unsat_core                   none
% 7.31/1.52  --bmc1_unsat_core_children              false
% 7.31/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.31/1.52  --bmc1_out_stat                         full
% 7.31/1.52  --bmc1_ground_init                      false
% 7.31/1.52  --bmc1_pre_inst_next_state              false
% 7.31/1.52  --bmc1_pre_inst_state                   false
% 7.31/1.52  --bmc1_pre_inst_reach_state             false
% 7.31/1.52  --bmc1_out_unsat_core                   false
% 7.31/1.52  --bmc1_aig_witness_out                  false
% 7.31/1.52  --bmc1_verbose                          false
% 7.31/1.52  --bmc1_dump_clauses_tptp                false
% 7.31/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.31/1.52  --bmc1_dump_file                        -
% 7.31/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.31/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.31/1.52  --bmc1_ucm_extend_mode                  1
% 7.31/1.52  --bmc1_ucm_init_mode                    2
% 7.31/1.52  --bmc1_ucm_cone_mode                    none
% 7.31/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.31/1.52  --bmc1_ucm_relax_model                  4
% 7.31/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.31/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.31/1.52  --bmc1_ucm_layered_model                none
% 7.31/1.52  --bmc1_ucm_max_lemma_size               10
% 7.31/1.52  
% 7.31/1.52  ------ AIG Options
% 7.31/1.52  
% 7.31/1.52  --aig_mode                              false
% 7.31/1.52  
% 7.31/1.52  ------ Instantiation Options
% 7.31/1.52  
% 7.31/1.52  --instantiation_flag                    true
% 7.31/1.52  --inst_sos_flag                         true
% 7.31/1.52  --inst_sos_phase                        true
% 7.31/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.31/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.31/1.52  --inst_lit_sel_side                     num_symb
% 7.31/1.52  --inst_solver_per_active                1400
% 7.31/1.52  --inst_solver_calls_frac                1.
% 7.31/1.52  --inst_passive_queue_type               priority_queues
% 7.31/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.31/1.52  --inst_passive_queues_freq              [25;2]
% 7.31/1.52  --inst_dismatching                      true
% 7.31/1.52  --inst_eager_unprocessed_to_passive     true
% 7.31/1.52  --inst_prop_sim_given                   true
% 7.31/1.52  --inst_prop_sim_new                     false
% 7.31/1.52  --inst_subs_new                         false
% 7.31/1.52  --inst_eq_res_simp                      false
% 7.31/1.52  --inst_subs_given                       false
% 7.31/1.52  --inst_orphan_elimination               true
% 7.31/1.52  --inst_learning_loop_flag               true
% 7.31/1.52  --inst_learning_start                   3000
% 7.31/1.52  --inst_learning_factor                  2
% 7.31/1.52  --inst_start_prop_sim_after_learn       3
% 7.31/1.52  --inst_sel_renew                        solver
% 7.31/1.52  --inst_lit_activity_flag                true
% 7.31/1.52  --inst_restr_to_given                   false
% 7.31/1.52  --inst_activity_threshold               500
% 7.31/1.52  --inst_out_proof                        true
% 7.31/1.52  
% 7.31/1.52  ------ Resolution Options
% 7.31/1.52  
% 7.31/1.52  --resolution_flag                       true
% 7.31/1.52  --res_lit_sel                           adaptive
% 7.31/1.52  --res_lit_sel_side                      none
% 7.31/1.52  --res_ordering                          kbo
% 7.31/1.52  --res_to_prop_solver                    active
% 7.31/1.52  --res_prop_simpl_new                    false
% 7.31/1.52  --res_prop_simpl_given                  true
% 7.31/1.52  --res_passive_queue_type                priority_queues
% 7.31/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.31/1.52  --res_passive_queues_freq               [15;5]
% 7.31/1.52  --res_forward_subs                      full
% 7.31/1.52  --res_backward_subs                     full
% 7.31/1.52  --res_forward_subs_resolution           true
% 7.31/1.52  --res_backward_subs_resolution          true
% 7.31/1.52  --res_orphan_elimination                true
% 7.31/1.52  --res_time_limit                        2.
% 7.31/1.52  --res_out_proof                         true
% 7.31/1.52  
% 7.31/1.52  ------ Superposition Options
% 7.31/1.52  
% 7.31/1.52  --superposition_flag                    true
% 7.31/1.52  --sup_passive_queue_type                priority_queues
% 7.31/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.31/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.31/1.52  --demod_completeness_check              fast
% 7.31/1.52  --demod_use_ground                      true
% 7.31/1.52  --sup_to_prop_solver                    passive
% 7.31/1.52  --sup_prop_simpl_new                    true
% 7.31/1.52  --sup_prop_simpl_given                  true
% 7.31/1.52  --sup_fun_splitting                     true
% 7.31/1.52  --sup_smt_interval                      50000
% 7.31/1.52  
% 7.31/1.52  ------ Superposition Simplification Setup
% 7.31/1.52  
% 7.31/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.31/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.31/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.31/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.31/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.31/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.31/1.52  --sup_immed_triv                        [TrivRules]
% 7.31/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.52  --sup_immed_bw_main                     []
% 7.31/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.31/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.31/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.52  --sup_input_bw                          []
% 7.31/1.52  
% 7.31/1.52  ------ Combination Options
% 7.31/1.52  
% 7.31/1.52  --comb_res_mult                         3
% 7.31/1.52  --comb_sup_mult                         2
% 7.31/1.52  --comb_inst_mult                        10
% 7.31/1.52  
% 7.31/1.52  ------ Debug Options
% 7.31/1.52  
% 7.31/1.52  --dbg_backtrace                         false
% 7.31/1.52  --dbg_dump_prop_clauses                 false
% 7.31/1.52  --dbg_dump_prop_clauses_file            -
% 7.31/1.52  --dbg_out_stat                          false
% 7.31/1.52  ------ Parsing...
% 7.31/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.31/1.52  
% 7.31/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.31/1.52  
% 7.31/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.31/1.52  
% 7.31/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.31/1.52  ------ Proving...
% 7.31/1.52  ------ Problem Properties 
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  clauses                                 17
% 7.31/1.52  conjectures                             3
% 7.31/1.52  EPR                                     0
% 7.31/1.52  Horn                                    15
% 7.31/1.52  unary                                   6
% 7.31/1.52  binary                                  3
% 7.31/1.52  lits                                    40
% 7.31/1.52  lits eq                                 15
% 7.31/1.52  fd_pure                                 0
% 7.31/1.52  fd_pseudo                               0
% 7.31/1.52  fd_cond                                 0
% 7.31/1.52  fd_pseudo_cond                          4
% 7.31/1.52  AC symbols                              0
% 7.31/1.52  
% 7.31/1.52  ------ Schedule dynamic 5 is on 
% 7.31/1.52  
% 7.31/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  ------ 
% 7.31/1.52  Current options:
% 7.31/1.52  ------ 
% 7.31/1.52  
% 7.31/1.52  ------ Input Options
% 7.31/1.52  
% 7.31/1.52  --out_options                           all
% 7.31/1.52  --tptp_safe_out                         true
% 7.31/1.52  --problem_path                          ""
% 7.31/1.52  --include_path                          ""
% 7.31/1.52  --clausifier                            res/vclausify_rel
% 7.31/1.52  --clausifier_options                    ""
% 7.31/1.52  --stdin                                 false
% 7.31/1.52  --stats_out                             all
% 7.31/1.52  
% 7.31/1.52  ------ General Options
% 7.31/1.52  
% 7.31/1.52  --fof                                   false
% 7.31/1.52  --time_out_real                         305.
% 7.31/1.52  --time_out_virtual                      -1.
% 7.31/1.52  --symbol_type_check                     false
% 7.31/1.52  --clausify_out                          false
% 7.31/1.52  --sig_cnt_out                           false
% 7.31/1.52  --trig_cnt_out                          false
% 7.31/1.52  --trig_cnt_out_tolerance                1.
% 7.31/1.52  --trig_cnt_out_sk_spl                   false
% 7.31/1.52  --abstr_cl_out                          false
% 7.31/1.52  
% 7.31/1.52  ------ Global Options
% 7.31/1.52  
% 7.31/1.52  --schedule                              default
% 7.31/1.52  --add_important_lit                     false
% 7.31/1.52  --prop_solver_per_cl                    1000
% 7.31/1.52  --min_unsat_core                        false
% 7.31/1.52  --soft_assumptions                      false
% 7.31/1.52  --soft_lemma_size                       3
% 7.31/1.52  --prop_impl_unit_size                   0
% 7.31/1.52  --prop_impl_unit                        []
% 7.31/1.52  --share_sel_clauses                     true
% 7.31/1.52  --reset_solvers                         false
% 7.31/1.52  --bc_imp_inh                            [conj_cone]
% 7.31/1.52  --conj_cone_tolerance                   3.
% 7.31/1.52  --extra_neg_conj                        none
% 7.31/1.52  --large_theory_mode                     true
% 7.31/1.52  --prolific_symb_bound                   200
% 7.31/1.52  --lt_threshold                          2000
% 7.31/1.52  --clause_weak_htbl                      true
% 7.31/1.52  --gc_record_bc_elim                     false
% 7.31/1.52  
% 7.31/1.52  ------ Preprocessing Options
% 7.31/1.52  
% 7.31/1.52  --preprocessing_flag                    true
% 7.31/1.52  --time_out_prep_mult                    0.1
% 7.31/1.52  --splitting_mode                        input
% 7.31/1.52  --splitting_grd                         true
% 7.31/1.52  --splitting_cvd                         false
% 7.31/1.52  --splitting_cvd_svl                     false
% 7.31/1.52  --splitting_nvd                         32
% 7.31/1.52  --sub_typing                            true
% 7.31/1.52  --prep_gs_sim                           true
% 7.31/1.52  --prep_unflatten                        true
% 7.31/1.52  --prep_res_sim                          true
% 7.31/1.52  --prep_upred                            true
% 7.31/1.52  --prep_sem_filter                       exhaustive
% 7.31/1.52  --prep_sem_filter_out                   false
% 7.31/1.52  --pred_elim                             true
% 7.31/1.52  --res_sim_input                         true
% 7.31/1.52  --eq_ax_congr_red                       true
% 7.31/1.52  --pure_diseq_elim                       true
% 7.31/1.52  --brand_transform                       false
% 7.31/1.52  --non_eq_to_eq                          false
% 7.31/1.52  --prep_def_merge                        true
% 7.31/1.52  --prep_def_merge_prop_impl              false
% 7.31/1.52  --prep_def_merge_mbd                    true
% 7.31/1.52  --prep_def_merge_tr_red                 false
% 7.31/1.52  --prep_def_merge_tr_cl                  false
% 7.31/1.52  --smt_preprocessing                     true
% 7.31/1.52  --smt_ac_axioms                         fast
% 7.31/1.52  --preprocessed_out                      false
% 7.31/1.52  --preprocessed_stats                    false
% 7.31/1.52  
% 7.31/1.52  ------ Abstraction refinement Options
% 7.31/1.52  
% 7.31/1.52  --abstr_ref                             []
% 7.31/1.52  --abstr_ref_prep                        false
% 7.31/1.52  --abstr_ref_until_sat                   false
% 7.31/1.52  --abstr_ref_sig_restrict                funpre
% 7.31/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.31/1.52  --abstr_ref_under                       []
% 7.31/1.52  
% 7.31/1.52  ------ SAT Options
% 7.31/1.52  
% 7.31/1.52  --sat_mode                              false
% 7.31/1.52  --sat_fm_restart_options                ""
% 7.31/1.52  --sat_gr_def                            false
% 7.31/1.52  --sat_epr_types                         true
% 7.31/1.52  --sat_non_cyclic_types                  false
% 7.31/1.52  --sat_finite_models                     false
% 7.31/1.52  --sat_fm_lemmas                         false
% 7.31/1.52  --sat_fm_prep                           false
% 7.31/1.52  --sat_fm_uc_incr                        true
% 7.31/1.52  --sat_out_model                         small
% 7.31/1.52  --sat_out_clauses                       false
% 7.31/1.52  
% 7.31/1.52  ------ QBF Options
% 7.31/1.52  
% 7.31/1.52  --qbf_mode                              false
% 7.31/1.52  --qbf_elim_univ                         false
% 7.31/1.52  --qbf_dom_inst                          none
% 7.31/1.52  --qbf_dom_pre_inst                      false
% 7.31/1.52  --qbf_sk_in                             false
% 7.31/1.52  --qbf_pred_elim                         true
% 7.31/1.52  --qbf_split                             512
% 7.31/1.52  
% 7.31/1.52  ------ BMC1 Options
% 7.31/1.52  
% 7.31/1.52  --bmc1_incremental                      false
% 7.31/1.52  --bmc1_axioms                           reachable_all
% 7.31/1.52  --bmc1_min_bound                        0
% 7.31/1.52  --bmc1_max_bound                        -1
% 7.31/1.52  --bmc1_max_bound_default                -1
% 7.31/1.52  --bmc1_symbol_reachability              true
% 7.31/1.52  --bmc1_property_lemmas                  false
% 7.31/1.52  --bmc1_k_induction                      false
% 7.31/1.52  --bmc1_non_equiv_states                 false
% 7.31/1.52  --bmc1_deadlock                         false
% 7.31/1.52  --bmc1_ucm                              false
% 7.31/1.52  --bmc1_add_unsat_core                   none
% 7.31/1.52  --bmc1_unsat_core_children              false
% 7.31/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.31/1.52  --bmc1_out_stat                         full
% 7.31/1.52  --bmc1_ground_init                      false
% 7.31/1.52  --bmc1_pre_inst_next_state              false
% 7.31/1.52  --bmc1_pre_inst_state                   false
% 7.31/1.52  --bmc1_pre_inst_reach_state             false
% 7.31/1.52  --bmc1_out_unsat_core                   false
% 7.31/1.52  --bmc1_aig_witness_out                  false
% 7.31/1.52  --bmc1_verbose                          false
% 7.31/1.52  --bmc1_dump_clauses_tptp                false
% 7.31/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.31/1.52  --bmc1_dump_file                        -
% 7.31/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.31/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.31/1.52  --bmc1_ucm_extend_mode                  1
% 7.31/1.52  --bmc1_ucm_init_mode                    2
% 7.31/1.52  --bmc1_ucm_cone_mode                    none
% 7.31/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.31/1.52  --bmc1_ucm_relax_model                  4
% 7.31/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.31/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.31/1.52  --bmc1_ucm_layered_model                none
% 7.31/1.52  --bmc1_ucm_max_lemma_size               10
% 7.31/1.52  
% 7.31/1.52  ------ AIG Options
% 7.31/1.52  
% 7.31/1.52  --aig_mode                              false
% 7.31/1.52  
% 7.31/1.52  ------ Instantiation Options
% 7.31/1.52  
% 7.31/1.52  --instantiation_flag                    true
% 7.31/1.52  --inst_sos_flag                         true
% 7.31/1.52  --inst_sos_phase                        true
% 7.31/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.31/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.31/1.52  --inst_lit_sel_side                     none
% 7.31/1.52  --inst_solver_per_active                1400
% 7.31/1.52  --inst_solver_calls_frac                1.
% 7.31/1.52  --inst_passive_queue_type               priority_queues
% 7.31/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.31/1.52  --inst_passive_queues_freq              [25;2]
% 7.31/1.52  --inst_dismatching                      true
% 7.31/1.52  --inst_eager_unprocessed_to_passive     true
% 7.31/1.52  --inst_prop_sim_given                   true
% 7.31/1.52  --inst_prop_sim_new                     false
% 7.31/1.52  --inst_subs_new                         false
% 7.31/1.52  --inst_eq_res_simp                      false
% 7.31/1.52  --inst_subs_given                       false
% 7.31/1.52  --inst_orphan_elimination               true
% 7.31/1.52  --inst_learning_loop_flag               true
% 7.31/1.52  --inst_learning_start                   3000
% 7.31/1.52  --inst_learning_factor                  2
% 7.31/1.52  --inst_start_prop_sim_after_learn       3
% 7.31/1.52  --inst_sel_renew                        solver
% 7.31/1.52  --inst_lit_activity_flag                true
% 7.31/1.52  --inst_restr_to_given                   false
% 7.31/1.52  --inst_activity_threshold               500
% 7.31/1.52  --inst_out_proof                        true
% 7.31/1.52  
% 7.31/1.52  ------ Resolution Options
% 7.31/1.52  
% 7.31/1.52  --resolution_flag                       false
% 7.31/1.52  --res_lit_sel                           adaptive
% 7.31/1.52  --res_lit_sel_side                      none
% 7.31/1.52  --res_ordering                          kbo
% 7.31/1.52  --res_to_prop_solver                    active
% 7.31/1.52  --res_prop_simpl_new                    false
% 7.31/1.52  --res_prop_simpl_given                  true
% 7.31/1.52  --res_passive_queue_type                priority_queues
% 7.31/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.31/1.52  --res_passive_queues_freq               [15;5]
% 7.31/1.52  --res_forward_subs                      full
% 7.31/1.52  --res_backward_subs                     full
% 7.31/1.52  --res_forward_subs_resolution           true
% 7.31/1.52  --res_backward_subs_resolution          true
% 7.31/1.52  --res_orphan_elimination                true
% 7.31/1.52  --res_time_limit                        2.
% 7.31/1.52  --res_out_proof                         true
% 7.31/1.52  
% 7.31/1.52  ------ Superposition Options
% 7.31/1.52  
% 7.31/1.52  --superposition_flag                    true
% 7.31/1.52  --sup_passive_queue_type                priority_queues
% 7.31/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.31/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.31/1.52  --demod_completeness_check              fast
% 7.31/1.52  --demod_use_ground                      true
% 7.31/1.52  --sup_to_prop_solver                    passive
% 7.31/1.52  --sup_prop_simpl_new                    true
% 7.31/1.52  --sup_prop_simpl_given                  true
% 7.31/1.52  --sup_fun_splitting                     true
% 7.31/1.52  --sup_smt_interval                      50000
% 7.31/1.52  
% 7.31/1.52  ------ Superposition Simplification Setup
% 7.31/1.52  
% 7.31/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.31/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.31/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.31/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.31/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.31/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.31/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.31/1.52  --sup_immed_triv                        [TrivRules]
% 7.31/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.52  --sup_immed_bw_main                     []
% 7.31/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.31/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.31/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.31/1.52  --sup_input_bw                          []
% 7.31/1.52  
% 7.31/1.52  ------ Combination Options
% 7.31/1.52  
% 7.31/1.52  --comb_res_mult                         3
% 7.31/1.52  --comb_sup_mult                         2
% 7.31/1.52  --comb_inst_mult                        10
% 7.31/1.52  
% 7.31/1.52  ------ Debug Options
% 7.31/1.52  
% 7.31/1.52  --dbg_backtrace                         false
% 7.31/1.52  --dbg_dump_prop_clauses                 false
% 7.31/1.52  --dbg_dump_prop_clauses_file            -
% 7.31/1.52  --dbg_out_stat                          false
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  ------ Proving...
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  % SZS status Theorem for theBenchmark.p
% 7.31/1.52  
% 7.31/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.31/1.52  
% 7.31/1.52  fof(f14,conjecture,(
% 7.31/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f15,negated_conjecture,(
% 7.31/1.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.31/1.52    inference(negated_conjecture,[],[f14])).
% 7.31/1.52  
% 7.31/1.52  fof(f26,plain,(
% 7.31/1.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.31/1.52    inference(ennf_transformation,[],[f15])).
% 7.31/1.52  
% 7.31/1.52  fof(f33,plain,(
% 7.31/1.52    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 7.31/1.52    introduced(choice_axiom,[])).
% 7.31/1.52  
% 7.31/1.52  fof(f32,plain,(
% 7.31/1.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.31/1.52    introduced(choice_axiom,[])).
% 7.31/1.52  
% 7.31/1.52  fof(f34,plain,(
% 7.31/1.52    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.31/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f33,f32])).
% 7.31/1.52  
% 7.31/1.52  fof(f56,plain,(
% 7.31/1.52    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.31/1.52    inference(cnf_transformation,[],[f34])).
% 7.31/1.52  
% 7.31/1.52  fof(f55,plain,(
% 7.31/1.52    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.31/1.52    inference(cnf_transformation,[],[f34])).
% 7.31/1.52  
% 7.31/1.52  fof(f10,axiom,(
% 7.31/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f19,plain,(
% 7.31/1.52    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.31/1.52    inference(ennf_transformation,[],[f10])).
% 7.31/1.52  
% 7.31/1.52  fof(f20,plain,(
% 7.31/1.52    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.31/1.52    inference(flattening,[],[f19])).
% 7.31/1.52  
% 7.31/1.52  fof(f51,plain,(
% 7.31/1.52    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.31/1.52    inference(cnf_transformation,[],[f20])).
% 7.31/1.52  
% 7.31/1.52  fof(f11,axiom,(
% 7.31/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f21,plain,(
% 7.31/1.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.31/1.52    inference(ennf_transformation,[],[f11])).
% 7.31/1.52  
% 7.31/1.52  fof(f52,plain,(
% 7.31/1.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.31/1.52    inference(cnf_transformation,[],[f21])).
% 7.31/1.52  
% 7.31/1.52  fof(f13,axiom,(
% 7.31/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f24,plain,(
% 7.31/1.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.31/1.52    inference(ennf_transformation,[],[f13])).
% 7.31/1.52  
% 7.31/1.52  fof(f25,plain,(
% 7.31/1.52    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.31/1.52    inference(flattening,[],[f24])).
% 7.31/1.52  
% 7.31/1.52  fof(f54,plain,(
% 7.31/1.52    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.31/1.52    inference(cnf_transformation,[],[f25])).
% 7.31/1.52  
% 7.31/1.52  fof(f9,axiom,(
% 7.31/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f18,plain,(
% 7.31/1.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.31/1.52    inference(ennf_transformation,[],[f9])).
% 7.31/1.52  
% 7.31/1.52  fof(f50,plain,(
% 7.31/1.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.31/1.52    inference(cnf_transformation,[],[f18])).
% 7.31/1.52  
% 7.31/1.52  fof(f57,plain,(
% 7.31/1.52    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 7.31/1.52    inference(cnf_transformation,[],[f34])).
% 7.31/1.52  
% 7.31/1.52  fof(f1,axiom,(
% 7.31/1.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f16,plain,(
% 7.31/1.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.31/1.52    inference(ennf_transformation,[],[f1])).
% 7.31/1.52  
% 7.31/1.52  fof(f27,plain,(
% 7.31/1.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.31/1.52    inference(nnf_transformation,[],[f16])).
% 7.31/1.52  
% 7.31/1.52  fof(f28,plain,(
% 7.31/1.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.31/1.52    inference(flattening,[],[f27])).
% 7.31/1.52  
% 7.31/1.52  fof(f29,plain,(
% 7.31/1.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.31/1.52    inference(rectify,[],[f28])).
% 7.31/1.52  
% 7.31/1.52  fof(f30,plain,(
% 7.31/1.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.31/1.52    introduced(choice_axiom,[])).
% 7.31/1.52  
% 7.31/1.52  fof(f31,plain,(
% 7.31/1.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.31/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.31/1.52  
% 7.31/1.52  fof(f37,plain,(
% 7.31/1.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.31/1.52    inference(cnf_transformation,[],[f31])).
% 7.31/1.52  
% 7.31/1.52  fof(f3,axiom,(
% 7.31/1.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f44,plain,(
% 7.31/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.31/1.52    inference(cnf_transformation,[],[f3])).
% 7.31/1.52  
% 7.31/1.52  fof(f4,axiom,(
% 7.31/1.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f45,plain,(
% 7.31/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.31/1.52    inference(cnf_transformation,[],[f4])).
% 7.31/1.52  
% 7.31/1.52  fof(f5,axiom,(
% 7.31/1.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f46,plain,(
% 7.31/1.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.31/1.52    inference(cnf_transformation,[],[f5])).
% 7.31/1.52  
% 7.31/1.52  fof(f6,axiom,(
% 7.31/1.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f47,plain,(
% 7.31/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.31/1.52    inference(cnf_transformation,[],[f6])).
% 7.31/1.52  
% 7.31/1.52  fof(f58,plain,(
% 7.31/1.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 7.31/1.52    inference(definition_unfolding,[],[f46,f47])).
% 7.31/1.52  
% 7.31/1.52  fof(f59,plain,(
% 7.31/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 7.31/1.52    inference(definition_unfolding,[],[f45,f58])).
% 7.31/1.52  
% 7.31/1.52  fof(f60,plain,(
% 7.31/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.31/1.52    inference(definition_unfolding,[],[f44,f59])).
% 7.31/1.52  
% 7.31/1.52  fof(f68,plain,(
% 7.31/1.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.31/1.52    inference(definition_unfolding,[],[f37,f60])).
% 7.31/1.52  
% 7.31/1.52  fof(f74,plain,(
% 7.31/1.52    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 7.31/1.52    inference(equality_resolution,[],[f68])).
% 7.31/1.52  
% 7.31/1.52  fof(f75,plain,(
% 7.31/1.52    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 7.31/1.52    inference(equality_resolution,[],[f74])).
% 7.31/1.52  
% 7.31/1.52  fof(f12,axiom,(
% 7.31/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f22,plain,(
% 7.31/1.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.31/1.52    inference(ennf_transformation,[],[f12])).
% 7.31/1.52  
% 7.31/1.52  fof(f23,plain,(
% 7.31/1.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.31/1.52    inference(flattening,[],[f22])).
% 7.31/1.52  
% 7.31/1.52  fof(f53,plain,(
% 7.31/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.31/1.52    inference(cnf_transformation,[],[f23])).
% 7.31/1.52  
% 7.31/1.52  fof(f8,axiom,(
% 7.31/1.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f49,plain,(
% 7.31/1.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.31/1.52    inference(cnf_transformation,[],[f8])).
% 7.31/1.52  
% 7.31/1.52  fof(f2,axiom,(
% 7.31/1.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f43,plain,(
% 7.31/1.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.31/1.52    inference(cnf_transformation,[],[f2])).
% 7.31/1.52  
% 7.31/1.52  fof(f61,plain,(
% 7.31/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 7.31/1.52    inference(definition_unfolding,[],[f43,f60])).
% 7.31/1.52  
% 7.31/1.52  fof(f62,plain,(
% 7.31/1.52    ( ! [X0,X1] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.31/1.52    inference(definition_unfolding,[],[f49,f61])).
% 7.31/1.52  
% 7.31/1.52  fof(f71,plain,(
% 7.31/1.52    ( ! [X2,X0,X1] : (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.31/1.52    inference(definition_unfolding,[],[f53,f62])).
% 7.31/1.52  
% 7.31/1.52  fof(f7,axiom,(
% 7.31/1.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 7.31/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.31/1.52  
% 7.31/1.52  fof(f17,plain,(
% 7.31/1.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 7.31/1.52    inference(ennf_transformation,[],[f7])).
% 7.31/1.52  
% 7.31/1.52  fof(f48,plain,(
% 7.31/1.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 7.31/1.52    inference(cnf_transformation,[],[f17])).
% 7.31/1.52  
% 7.31/1.52  cnf(c_15,negated_conjecture,
% 7.31/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.31/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_738,plain,
% 7.31/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_16,negated_conjecture,
% 7.31/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.31/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_737,plain,
% 7.31/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_10,plain,
% 7.31/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.31/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.31/1.52      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.31/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_743,plain,
% 7.31/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.31/1.52      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.31/1.52      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_11,plain,
% 7.31/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.31/1.52      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.31/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_742,plain,
% 7.31/1.52      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.31/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_1268,plain,
% 7.31/1.52      ( k3_subset_1(X0,k3_subset_1(X0,k4_subset_1(X0,X1,X2))) = k4_subset_1(X0,X1,X2)
% 7.31/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.31/1.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_743,c_742]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_3648,plain,
% 7.31/1.52      ( k3_subset_1(sK1,k3_subset_1(sK1,k4_subset_1(sK1,sK2,X0))) = k4_subset_1(sK1,sK2,X0)
% 7.31/1.52      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_737,c_1268]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_4392,plain,
% 7.31/1.52      ( k3_subset_1(sK1,k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3))) = k4_subset_1(sK1,sK2,sK3) ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_738,c_3648]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_13,plain,
% 7.31/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.31/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.31/1.52      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 7.31/1.52      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 7.31/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_740,plain,
% 7.31/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.31/1.52      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.31/1.52      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
% 7.31/1.52      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_4401,plain,
% 7.31/1.52      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 7.31/1.52      | m1_subset_1(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k1_zfmisc_1(sK1)) != iProver_top
% 7.31/1.52      | r1_tarski(X0,k4_subset_1(sK1,sK2,sK3)) != iProver_top
% 7.31/1.52      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,X0)) = iProver_top ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_4392,c_740]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_17,plain,
% 7.31/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_18,plain,
% 7.31/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_9,plain,
% 7.31/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.31/1.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.31/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_782,plain,
% 7.31/1.52      ( ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 7.31/1.52      | m1_subset_1(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k1_zfmisc_1(sK1)) ),
% 7.31/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_783,plain,
% 7.31/1.52      ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 7.31/1.52      | m1_subset_1(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_811,plain,
% 7.31/1.52      ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
% 7.31/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 7.31/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.31/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_812,plain,
% 7.31/1.52      ( m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 7.31/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.31/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_29714,plain,
% 7.31/1.52      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 7.31/1.52      | r1_tarski(X0,k4_subset_1(sK1,sK2,sK3)) != iProver_top
% 7.31/1.52      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,X0)) = iProver_top ),
% 7.31/1.52      inference(global_propositional_subsumption,
% 7.31/1.52                [status(thm)],
% 7.31/1.52                [c_4401,c_17,c_18,c_783,c_812]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_14,negated_conjecture,
% 7.31/1.52      ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
% 7.31/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_739,plain,
% 7.31/1.52      ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) != iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_29805,plain,
% 7.31/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 7.31/1.52      | r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3)) != iProver_top ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_29714,c_739]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_5,plain,
% 7.31/1.52      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) ),
% 7.31/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_748,plain,
% 7.31/1.52      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_12,plain,
% 7.31/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.31/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.31/1.52      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 7.31/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_741,plain,
% 7.31/1.52      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 7.31/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.31/1.52      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_1340,plain,
% 7.31/1.52      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
% 7.31/1.52      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_737,c_741]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_1720,plain,
% 7.31/1.52      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k4_subset_1(sK1,sK2,sK3) ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_738,c_1340]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_8,plain,
% 7.31/1.52      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 7.31/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_745,plain,
% 7.31/1.52      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 7.31/1.52      | r2_hidden(X0,X1) != iProver_top ),
% 7.31/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_1728,plain,
% 7.31/1.52      ( r1_tarski(X0,k4_subset_1(sK1,sK2,sK3)) = iProver_top
% 7.31/1.52      | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_1720,c_745]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(c_2762,plain,
% 7.31/1.52      ( r1_tarski(sK2,k4_subset_1(sK1,sK2,sK3)) = iProver_top ),
% 7.31/1.52      inference(superposition,[status(thm)],[c_748,c_1728]) ).
% 7.31/1.52  
% 7.31/1.52  cnf(contradiction,plain,
% 7.31/1.52      ( $false ),
% 7.31/1.52      inference(minisat,[status(thm)],[c_29805,c_2762,c_17]) ).
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.31/1.52  
% 7.31/1.52  ------                               Statistics
% 7.31/1.52  
% 7.31/1.52  ------ General
% 7.31/1.52  
% 7.31/1.52  abstr_ref_over_cycles:                  0
% 7.31/1.52  abstr_ref_under_cycles:                 0
% 7.31/1.52  gc_basic_clause_elim:                   0
% 7.31/1.52  forced_gc_time:                         0
% 7.31/1.52  parsing_time:                           0.005
% 7.31/1.52  unif_index_cands_time:                  0.
% 7.31/1.52  unif_index_add_time:                    0.
% 7.31/1.52  orderings_time:                         0.
% 7.31/1.52  out_proof_time:                         0.012
% 7.31/1.52  total_time:                             0.998
% 7.31/1.52  num_of_symbols:                         43
% 7.31/1.52  num_of_terms:                           57650
% 7.31/1.52  
% 7.31/1.52  ------ Preprocessing
% 7.31/1.52  
% 7.31/1.52  num_of_splits:                          0
% 7.31/1.52  num_of_split_atoms:                     0
% 7.31/1.52  num_of_reused_defs:                     0
% 7.31/1.52  num_eq_ax_congr_red:                    22
% 7.31/1.52  num_of_sem_filtered_clauses:            1
% 7.31/1.52  num_of_subtypes:                        0
% 7.31/1.52  monotx_restored_types:                  0
% 7.31/1.52  sat_num_of_epr_types:                   0
% 7.31/1.52  sat_num_of_non_cyclic_types:            0
% 7.31/1.52  sat_guarded_non_collapsed_types:        0
% 7.31/1.52  num_pure_diseq_elim:                    0
% 7.31/1.52  simp_replaced_by:                       0
% 7.31/1.52  res_preprocessed:                       70
% 7.31/1.52  prep_upred:                             0
% 7.31/1.52  prep_unflattend:                        22
% 7.31/1.52  smt_new_axioms:                         0
% 7.31/1.52  pred_elim_cands:                        3
% 7.31/1.52  pred_elim:                              0
% 7.31/1.52  pred_elim_cl:                           0
% 7.31/1.52  pred_elim_cycles:                       1
% 7.31/1.52  merged_defs:                            0
% 7.31/1.52  merged_defs_ncl:                        0
% 7.31/1.52  bin_hyper_res:                          0
% 7.31/1.52  prep_cycles:                            3
% 7.31/1.52  pred_elim_time:                         0.002
% 7.31/1.52  splitting_time:                         0.
% 7.31/1.52  sem_filter_time:                        0.
% 7.31/1.52  monotx_time:                            0.
% 7.31/1.52  subtype_inf_time:                       0.
% 7.31/1.52  
% 7.31/1.52  ------ Problem properties
% 7.31/1.52  
% 7.31/1.52  clauses:                                17
% 7.31/1.52  conjectures:                            3
% 7.31/1.52  epr:                                    0
% 7.31/1.52  horn:                                   15
% 7.31/1.52  ground:                                 3
% 7.31/1.52  unary:                                  6
% 7.31/1.52  binary:                                 3
% 7.31/1.52  lits:                                   40
% 7.31/1.52  lits_eq:                                15
% 7.31/1.52  fd_pure:                                0
% 7.31/1.52  fd_pseudo:                              0
% 7.31/1.52  fd_cond:                                0
% 7.31/1.52  fd_pseudo_cond:                         4
% 7.31/1.52  ac_symbols:                             0
% 7.31/1.52  
% 7.31/1.52  ------ Propositional Solver
% 7.31/1.52  
% 7.31/1.52  prop_solver_calls:                      30
% 7.31/1.52  prop_fast_solver_calls:                 943
% 7.31/1.52  smt_solver_calls:                       0
% 7.31/1.52  smt_fast_solver_calls:                  0
% 7.31/1.52  prop_num_of_clauses:                    14482
% 7.31/1.52  prop_preprocess_simplified:             23214
% 7.31/1.52  prop_fo_subsumed:                       31
% 7.31/1.52  prop_solver_time:                       0.
% 7.31/1.52  smt_solver_time:                        0.
% 7.31/1.52  smt_fast_solver_time:                   0.
% 7.31/1.52  prop_fast_solver_time:                  0.
% 7.31/1.52  prop_unsat_core_time:                   0.001
% 7.31/1.52  
% 7.31/1.52  ------ QBF
% 7.31/1.52  
% 7.31/1.52  qbf_q_res:                              0
% 7.31/1.52  qbf_num_tautologies:                    0
% 7.31/1.52  qbf_prep_cycles:                        0
% 7.31/1.52  
% 7.31/1.52  ------ BMC1
% 7.31/1.52  
% 7.31/1.52  bmc1_current_bound:                     -1
% 7.31/1.52  bmc1_last_solved_bound:                 -1
% 7.31/1.52  bmc1_unsat_core_size:                   -1
% 7.31/1.52  bmc1_unsat_core_parents_size:           -1
% 7.31/1.52  bmc1_merge_next_fun:                    0
% 7.31/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.31/1.52  
% 7.31/1.52  ------ Instantiation
% 7.31/1.52  
% 7.31/1.52  inst_num_of_clauses:                    3799
% 7.31/1.52  inst_num_in_passive:                    2212
% 7.31/1.52  inst_num_in_active:                     1518
% 7.31/1.52  inst_num_in_unprocessed:                69
% 7.31/1.52  inst_num_of_loops:                      1600
% 7.31/1.52  inst_num_of_learning_restarts:          0
% 7.31/1.52  inst_num_moves_active_passive:          79
% 7.31/1.52  inst_lit_activity:                      0
% 7.31/1.52  inst_lit_activity_moves:                2
% 7.31/1.52  inst_num_tautologies:                   0
% 7.31/1.52  inst_num_prop_implied:                  0
% 7.31/1.52  inst_num_existing_simplified:           0
% 7.31/1.52  inst_num_eq_res_simplified:             0
% 7.31/1.52  inst_num_child_elim:                    0
% 7.31/1.52  inst_num_of_dismatching_blockings:      5189
% 7.31/1.52  inst_num_of_non_proper_insts:           4099
% 7.31/1.52  inst_num_of_duplicates:                 0
% 7.31/1.52  inst_inst_num_from_inst_to_res:         0
% 7.31/1.52  inst_dismatching_checking_time:         0.
% 7.31/1.52  
% 7.31/1.52  ------ Resolution
% 7.31/1.52  
% 7.31/1.52  res_num_of_clauses:                     0
% 7.31/1.52  res_num_in_passive:                     0
% 7.31/1.52  res_num_in_active:                      0
% 7.31/1.52  res_num_of_loops:                       73
% 7.31/1.52  res_forward_subset_subsumed:            348
% 7.31/1.52  res_backward_subset_subsumed:           0
% 7.31/1.52  res_forward_subsumed:                   0
% 7.31/1.52  res_backward_subsumed:                  0
% 7.31/1.52  res_forward_subsumption_resolution:     0
% 7.31/1.52  res_backward_subsumption_resolution:    0
% 7.31/1.52  res_clause_to_clause_subsumption:       4251
% 7.31/1.52  res_orphan_elimination:                 0
% 7.31/1.52  res_tautology_del:                      172
% 7.31/1.52  res_num_eq_res_simplified:              0
% 7.31/1.52  res_num_sel_changes:                    0
% 7.31/1.52  res_moves_from_active_to_pass:          0
% 7.31/1.52  
% 7.31/1.52  ------ Superposition
% 7.31/1.52  
% 7.31/1.52  sup_time_total:                         0.
% 7.31/1.52  sup_time_generating:                    0.
% 7.31/1.52  sup_time_sim_full:                      0.
% 7.31/1.52  sup_time_sim_immed:                     0.
% 7.31/1.52  
% 7.31/1.52  sup_num_of_clauses:                     2017
% 7.31/1.52  sup_num_in_active:                      320
% 7.31/1.52  sup_num_in_passive:                     1697
% 7.31/1.52  sup_num_of_loops:                       319
% 7.31/1.52  sup_fw_superposition:                   1261
% 7.31/1.52  sup_bw_superposition:                   1215
% 7.31/1.52  sup_immediate_simplified:               303
% 7.31/1.52  sup_given_eliminated:                   0
% 7.31/1.52  comparisons_done:                       0
% 7.31/1.52  comparisons_avoided:                    30
% 7.31/1.52  
% 7.31/1.52  ------ Simplifications
% 7.31/1.52  
% 7.31/1.52  
% 7.31/1.52  sim_fw_subset_subsumed:                 2
% 7.31/1.52  sim_bw_subset_subsumed:                 0
% 7.31/1.52  sim_fw_subsumed:                        0
% 7.31/1.52  sim_bw_subsumed:                        0
% 7.31/1.52  sim_fw_subsumption_res:                 0
% 7.31/1.52  sim_bw_subsumption_res:                 0
% 7.31/1.52  sim_tautology_del:                      10
% 7.31/1.52  sim_eq_tautology_del:                   269
% 7.31/1.52  sim_eq_res_simp:                        0
% 7.31/1.52  sim_fw_demodulated:                     48
% 7.31/1.52  sim_bw_demodulated:                     0
% 7.31/1.52  sim_light_normalised:                   253
% 7.31/1.52  sim_joinable_taut:                      0
% 7.31/1.52  sim_joinable_simp:                      0
% 7.31/1.52  sim_ac_normalised:                      0
% 7.31/1.52  sim_smt_subsumption:                    0
% 7.31/1.52  
%------------------------------------------------------------------------------
