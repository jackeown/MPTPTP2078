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
% DateTime   : Thu Dec  3 11:39:36 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 272 expanded)
%              Number of clauses        :   51 (  80 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 ( 888 expanded)
%              Number of equality atoms :   81 ( 159 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f36,f35])).

fof(f62,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f40,f40])).

fof(f63,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f46,f64,f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f11])).

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
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_749,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_747,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_752,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2221,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_747,c_752])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_766,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2418,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_766])).

cnf(c_3081,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(k3_subset_1(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_2418])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_767,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3101,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_767])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_748,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2220,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_748,c_752])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_762,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3604,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k3_subset_1(sK1,sK3),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_762])).

cnf(c_4057,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_3604])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4316,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4057,c_26])).

cnf(c_5703,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3101,c_26,c_4057])).

cnf(c_7,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2400,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_subset_1(sK1,sK3))) = sK1 ),
    inference(superposition,[status(thm)],[c_2220,c_7])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_761,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5799,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,sK3)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2400,c_761])).

cnf(c_19311,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK1,sK3)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5703,c_5799])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_953,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_954,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1093,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1094,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_19460,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19311,c_23,c_29,c_954,c_1094])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_764,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1104,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_764])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_763,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3348,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_763])).

cnf(c_19467,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19460,c_3348])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19467,c_4316])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.59/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.52  
% 7.59/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.52  
% 7.59/1.52  ------  iProver source info
% 7.59/1.52  
% 7.59/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.52  git: non_committed_changes: false
% 7.59/1.52  git: last_make_outside_of_git: false
% 7.59/1.52  
% 7.59/1.52  ------ 
% 7.59/1.52  ------ Parsing...
% 7.59/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.52  
% 7.59/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.52  ------ Proving...
% 7.59/1.52  ------ Problem Properties 
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  clauses                                 23
% 7.59/1.52  conjectures                             4
% 7.59/1.52  EPR                                     6
% 7.59/1.52  Horn                                    19
% 7.59/1.52  unary                                   6
% 7.59/1.52  binary                                  9
% 7.59/1.52  lits                                    48
% 7.59/1.52  lits eq                                 5
% 7.59/1.52  fd_pure                                 0
% 7.59/1.52  fd_pseudo                               0
% 7.59/1.52  fd_cond                                 0
% 7.59/1.52  fd_pseudo_cond                          2
% 7.59/1.52  AC symbols                              0
% 7.59/1.52  
% 7.59/1.52  ------ Input Options Time Limit: Unbounded
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  ------ 
% 7.59/1.52  Current options:
% 7.59/1.52  ------ 
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  ------ Proving...
% 7.59/1.52  
% 7.59/1.52  
% 7.59/1.52  % SZS status Theorem for theBenchmark.p
% 7.59/1.52  
% 7.59/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.52  
% 7.59/1.52  fof(f16,conjecture,(
% 7.59/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f17,negated_conjecture,(
% 7.59/1.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.59/1.52    inference(negated_conjecture,[],[f16])).
% 7.59/1.52  
% 7.59/1.52  fof(f27,plain,(
% 7.59/1.52    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.59/1.52    inference(ennf_transformation,[],[f17])).
% 7.59/1.52  
% 7.59/1.52  fof(f33,plain,(
% 7.59/1.52    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.59/1.52    inference(nnf_transformation,[],[f27])).
% 7.59/1.52  
% 7.59/1.52  fof(f34,plain,(
% 7.59/1.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.59/1.52    inference(flattening,[],[f33])).
% 7.59/1.52  
% 7.59/1.52  fof(f36,plain,(
% 7.59/1.52    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 7.59/1.52    introduced(choice_axiom,[])).
% 7.59/1.52  
% 7.59/1.52  fof(f35,plain,(
% 7.59/1.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.59/1.52    introduced(choice_axiom,[])).
% 7.59/1.52  
% 7.59/1.52  fof(f37,plain,(
% 7.59/1.52    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.59/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f36,f35])).
% 7.59/1.52  
% 7.59/1.52  fof(f62,plain,(
% 7.59/1.52    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 7.59/1.52    inference(cnf_transformation,[],[f37])).
% 7.59/1.52  
% 7.59/1.52  fof(f60,plain,(
% 7.59/1.52    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.59/1.52    inference(cnf_transformation,[],[f37])).
% 7.59/1.52  
% 7.59/1.52  fof(f14,axiom,(
% 7.59/1.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f26,plain,(
% 7.59/1.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.59/1.52    inference(ennf_transformation,[],[f14])).
% 7.59/1.52  
% 7.59/1.52  fof(f58,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.59/1.52    inference(cnf_transformation,[],[f26])).
% 7.59/1.52  
% 7.59/1.52  fof(f3,axiom,(
% 7.59/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f40,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.59/1.52    inference(cnf_transformation,[],[f3])).
% 7.59/1.52  
% 7.59/1.52  fof(f70,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.59/1.52    inference(definition_unfolding,[],[f58,f40])).
% 7.59/1.52  
% 7.59/1.52  fof(f4,axiom,(
% 7.59/1.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f19,plain,(
% 7.59/1.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.59/1.52    inference(ennf_transformation,[],[f4])).
% 7.59/1.52  
% 7.59/1.52  fof(f42,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 7.59/1.52    inference(cnf_transformation,[],[f19])).
% 7.59/1.52  
% 7.59/1.52  fof(f65,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 7.59/1.52    inference(definition_unfolding,[],[f42,f40])).
% 7.59/1.52  
% 7.59/1.52  fof(f2,axiom,(
% 7.59/1.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f18,plain,(
% 7.59/1.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.59/1.52    inference(ennf_transformation,[],[f2])).
% 7.59/1.52  
% 7.59/1.52  fof(f39,plain,(
% 7.59/1.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f18])).
% 7.59/1.52  
% 7.59/1.52  fof(f61,plain,(
% 7.59/1.52    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.59/1.52    inference(cnf_transformation,[],[f37])).
% 7.59/1.52  
% 7.59/1.52  fof(f7,axiom,(
% 7.59/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f22,plain,(
% 7.59/1.52    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.59/1.52    inference(ennf_transformation,[],[f7])).
% 7.59/1.52  
% 7.59/1.52  fof(f45,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f22])).
% 7.59/1.52  
% 7.59/1.52  fof(f67,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) | ~r1_tarski(X0,X1)) )),
% 7.59/1.52    inference(definition_unfolding,[],[f45,f40,f40])).
% 7.59/1.52  
% 7.59/1.52  fof(f63,plain,(
% 7.59/1.52    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 7.59/1.52    inference(cnf_transformation,[],[f37])).
% 7.59/1.52  
% 7.59/1.52  fof(f8,axiom,(
% 7.59/1.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f46,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.59/1.52    inference(cnf_transformation,[],[f8])).
% 7.59/1.52  
% 7.59/1.52  fof(f12,axiom,(
% 7.59/1.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f53,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.59/1.52    inference(cnf_transformation,[],[f12])).
% 7.59/1.52  
% 7.59/1.52  fof(f10,axiom,(
% 7.59/1.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f48,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f10])).
% 7.59/1.52  
% 7.59/1.52  fof(f64,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.59/1.52    inference(definition_unfolding,[],[f53,f48])).
% 7.59/1.52  
% 7.59/1.52  fof(f68,plain,(
% 7.59/1.52    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 7.59/1.52    inference(definition_unfolding,[],[f46,f64,f40])).
% 7.59/1.52  
% 7.59/1.52  fof(f9,axiom,(
% 7.59/1.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f23,plain,(
% 7.59/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 7.59/1.52    inference(ennf_transformation,[],[f9])).
% 7.59/1.52  
% 7.59/1.52  fof(f24,plain,(
% 7.59/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.59/1.52    inference(flattening,[],[f23])).
% 7.59/1.52  
% 7.59/1.52  fof(f47,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.59/1.52    inference(cnf_transformation,[],[f24])).
% 7.59/1.52  
% 7.59/1.52  fof(f69,plain,(
% 7.59/1.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 7.59/1.52    inference(definition_unfolding,[],[f47,f64])).
% 7.59/1.52  
% 7.59/1.52  fof(f15,axiom,(
% 7.59/1.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f59,plain,(
% 7.59/1.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.59/1.52    inference(cnf_transformation,[],[f15])).
% 7.59/1.52  
% 7.59/1.52  fof(f13,axiom,(
% 7.59/1.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f25,plain,(
% 7.59/1.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.59/1.52    inference(ennf_transformation,[],[f13])).
% 7.59/1.52  
% 7.59/1.52  fof(f32,plain,(
% 7.59/1.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.59/1.52    inference(nnf_transformation,[],[f25])).
% 7.59/1.52  
% 7.59/1.52  fof(f54,plain,(
% 7.59/1.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.59/1.52    inference(cnf_transformation,[],[f32])).
% 7.59/1.52  
% 7.59/1.52  fof(f11,axiom,(
% 7.59/1.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.59/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.52  
% 7.59/1.52  fof(f28,plain,(
% 7.59/1.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.59/1.52    inference(nnf_transformation,[],[f11])).
% 7.59/1.52  
% 7.59/1.52  fof(f29,plain,(
% 7.59/1.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.59/1.52    inference(rectify,[],[f28])).
% 7.59/1.52  
% 7.59/1.52  fof(f30,plain,(
% 7.59/1.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.59/1.53    introduced(choice_axiom,[])).
% 7.59/1.53  
% 7.59/1.53  fof(f31,plain,(
% 7.59/1.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.59/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.59/1.53  
% 7.59/1.53  fof(f49,plain,(
% 7.59/1.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.59/1.53    inference(cnf_transformation,[],[f31])).
% 7.59/1.53  
% 7.59/1.53  fof(f72,plain,(
% 7.59/1.53    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.59/1.53    inference(equality_resolution,[],[f49])).
% 7.59/1.53  
% 7.59/1.53  fof(f1,axiom,(
% 7.59/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.59/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.53  
% 7.59/1.53  fof(f38,plain,(
% 7.59/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.59/1.53    inference(cnf_transformation,[],[f1])).
% 7.59/1.53  
% 7.59/1.53  fof(f5,axiom,(
% 7.59/1.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.59/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.53  
% 7.59/1.53  fof(f43,plain,(
% 7.59/1.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.59/1.53    inference(cnf_transformation,[],[f5])).
% 7.59/1.53  
% 7.59/1.53  fof(f6,axiom,(
% 7.59/1.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.59/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.53  
% 7.59/1.53  fof(f20,plain,(
% 7.59/1.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.59/1.53    inference(ennf_transformation,[],[f6])).
% 7.59/1.53  
% 7.59/1.53  fof(f21,plain,(
% 7.59/1.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.59/1.53    inference(flattening,[],[f20])).
% 7.59/1.53  
% 7.59/1.53  fof(f44,plain,(
% 7.59/1.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.59/1.53    inference(cnf_transformation,[],[f21])).
% 7.59/1.53  
% 7.59/1.53  cnf(c_20,negated_conjecture,
% 7.59/1.53      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.59/1.53      | r1_tarski(sK2,sK3) ),
% 7.59/1.53      inference(cnf_transformation,[],[f62]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_749,plain,
% 7.59/1.53      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.59/1.53      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_22,negated_conjecture,
% 7.59/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.59/1.53      inference(cnf_transformation,[],[f60]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_747,plain,
% 7.59/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_17,plain,
% 7.59/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.59/1.53      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.59/1.53      inference(cnf_transformation,[],[f70]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_752,plain,
% 7.59/1.53      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.59/1.53      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_2221,plain,
% 7.59/1.53      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_747,c_752]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_2,plain,
% 7.59/1.53      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 7.59/1.53      | r1_xboole_0(X0,X2) ),
% 7.59/1.53      inference(cnf_transformation,[],[f65]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_766,plain,
% 7.59/1.53      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 7.59/1.53      | r1_xboole_0(X0,X2) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_2418,plain,
% 7.59/1.53      ( r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
% 7.59/1.53      | r1_xboole_0(X0,sK2) = iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_2221,c_766]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_3081,plain,
% 7.59/1.53      ( r1_tarski(sK2,sK3) = iProver_top
% 7.59/1.53      | r1_xboole_0(k3_subset_1(sK1,sK3),sK2) = iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_749,c_2418]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_1,plain,
% 7.59/1.53      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.59/1.53      inference(cnf_transformation,[],[f39]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_767,plain,
% 7.59/1.53      ( r1_xboole_0(X0,X1) != iProver_top
% 7.59/1.53      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_3101,plain,
% 7.59/1.53      ( r1_tarski(sK2,sK3) = iProver_top
% 7.59/1.53      | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_3081,c_767]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_21,negated_conjecture,
% 7.59/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.59/1.53      inference(cnf_transformation,[],[f61]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_748,plain,
% 7.59/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_2220,plain,
% 7.59/1.53      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_748,c_752]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_6,plain,
% 7.59/1.53      ( ~ r1_tarski(X0,X1)
% 7.59/1.53      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
% 7.59/1.53      inference(cnf_transformation,[],[f67]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_762,plain,
% 7.59/1.53      ( r1_tarski(X0,X1) != iProver_top
% 7.59/1.53      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_3604,plain,
% 7.59/1.53      ( r1_tarski(X0,sK3) != iProver_top
% 7.59/1.53      | r1_tarski(k3_subset_1(sK1,sK3),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_2220,c_762]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_4057,plain,
% 7.59/1.53      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.59/1.53      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_2221,c_3604]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_19,negated_conjecture,
% 7.59/1.53      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.59/1.53      | ~ r1_tarski(sK2,sK3) ),
% 7.59/1.53      inference(cnf_transformation,[],[f63]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_26,plain,
% 7.59/1.53      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 7.59/1.53      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_4316,plain,
% 7.59/1.53      ( r1_tarski(sK2,sK3) != iProver_top ),
% 7.59/1.53      inference(global_propositional_subsumption,
% 7.59/1.53                [status(thm)],
% 7.59/1.53                [c_4057,c_26]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_5703,plain,
% 7.59/1.53      ( r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 7.59/1.53      inference(global_propositional_subsumption,
% 7.59/1.53                [status(thm)],
% 7.59/1.53                [c_3101,c_26,c_4057]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_7,plain,
% 7.59/1.53      ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 7.59/1.53      inference(cnf_transformation,[],[f68]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_2400,plain,
% 7.59/1.53      ( k3_tarski(k1_enumset1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK1,sK3),k3_subset_1(sK1,sK3))) = sK1 ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_2220,c_7]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_8,plain,
% 7.59/1.53      ( r1_tarski(X0,X1)
% 7.59/1.53      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
% 7.59/1.53      | ~ r1_xboole_0(X0,X2) ),
% 7.59/1.53      inference(cnf_transformation,[],[f69]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_761,plain,
% 7.59/1.53      ( r1_tarski(X0,X1) = iProver_top
% 7.59/1.53      | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) != iProver_top
% 7.59/1.53      | r1_xboole_0(X0,X2) != iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_5799,plain,
% 7.59/1.53      ( r1_tarski(X0,k3_xboole_0(sK1,sK3)) = iProver_top
% 7.59/1.53      | r1_tarski(X0,sK1) != iProver_top
% 7.59/1.53      | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_2400,c_761]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_19311,plain,
% 7.59/1.53      ( r1_tarski(sK2,k3_xboole_0(sK1,sK3)) = iProver_top
% 7.59/1.53      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_5703,c_5799]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_23,plain,
% 7.59/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_18,plain,
% 7.59/1.53      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.59/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_27,plain,
% 7.59/1.53      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_29,plain,
% 7.59/1.53      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 7.59/1.53      inference(instantiation,[status(thm)],[c_27]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_16,plain,
% 7.59/1.53      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.59/1.53      inference(cnf_transformation,[],[f54]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_953,plain,
% 7.59/1.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 7.59/1.53      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 7.59/1.53      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.59/1.53      inference(instantiation,[status(thm)],[c_16]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_954,plain,
% 7.59/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 7.59/1.53      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 7.59/1.53      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_12,plain,
% 7.59/1.53      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.59/1.53      inference(cnf_transformation,[],[f72]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_1093,plain,
% 7.59/1.53      ( ~ r2_hidden(sK2,k1_zfmisc_1(sK1)) | r1_tarski(sK2,sK1) ),
% 7.59/1.53      inference(instantiation,[status(thm)],[c_12]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_1094,plain,
% 7.59/1.53      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 7.59/1.53      | r1_tarski(sK2,sK1) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_19460,plain,
% 7.59/1.53      ( r1_tarski(sK2,k3_xboole_0(sK1,sK3)) = iProver_top ),
% 7.59/1.53      inference(global_propositional_subsumption,
% 7.59/1.53                [status(thm)],
% 7.59/1.53                [c_19311,c_23,c_29,c_954,c_1094]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_0,plain,
% 7.59/1.53      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.59/1.53      inference(cnf_transformation,[],[f38]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_4,plain,
% 7.59/1.53      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.59/1.53      inference(cnf_transformation,[],[f43]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_764,plain,
% 7.59/1.53      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_1104,plain,
% 7.59/1.53      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_0,c_764]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_5,plain,
% 7.59/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.59/1.53      inference(cnf_transformation,[],[f44]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_763,plain,
% 7.59/1.53      ( r1_tarski(X0,X1) != iProver_top
% 7.59/1.53      | r1_tarski(X2,X0) != iProver_top
% 7.59/1.53      | r1_tarski(X2,X1) = iProver_top ),
% 7.59/1.53      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_3348,plain,
% 7.59/1.53      ( r1_tarski(X0,X1) = iProver_top
% 7.59/1.53      | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_1104,c_763]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(c_19467,plain,
% 7.59/1.53      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.59/1.53      inference(superposition,[status(thm)],[c_19460,c_3348]) ).
% 7.59/1.53  
% 7.59/1.53  cnf(contradiction,plain,
% 7.59/1.53      ( $false ),
% 7.59/1.53      inference(minisat,[status(thm)],[c_19467,c_4316]) ).
% 7.59/1.53  
% 7.59/1.53  
% 7.59/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.53  
% 7.59/1.53  ------                               Statistics
% 7.59/1.53  
% 7.59/1.53  ------ Selected
% 7.59/1.53  
% 7.59/1.53  total_time:                             0.508
% 7.59/1.53  
%------------------------------------------------------------------------------
