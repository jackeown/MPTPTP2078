%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:17 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 613 expanded)
%              Number of clauses        :   78 ( 209 expanded)
%              Number of leaves         :   19 ( 132 expanded)
%              Depth                    :   27
%              Number of atoms          :  365 (1611 expanded)
%              Number of equality atoms :  147 ( 551 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK3
      & r1_tarski(sK3,k3_subset_1(sK2,sK4))
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_xboole_0 != sK3
    & r1_tarski(sK3,k3_subset_1(sK2,sK4))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f36])).

fof(f61,plain,(
    r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X1)
      | k2_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X1)
      | k3_subset_1(X0,k1_xboole_0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)),k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k1_xboole_0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f62,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_959,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_129,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_1])).

cnf(c_130,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_944,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_130])).

cnf(c_1441,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_944])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_947,plain,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_945,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_952,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1524,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_945,c_952])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(k3_subset_1(sK2,sK4),k3_subset_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_951])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_962,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2346,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X1,k3_subset_1(sK2,X0)) = iProver_top
    | r1_tarski(X1,k3_subset_1(sK2,sK4)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1604,c_962])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8317,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_8318,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8317])).

cnf(c_10913,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X1,k3_subset_1(sK2,X0)) = iProver_top
    | r1_tarski(X1,k3_subset_1(sK2,sK4)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2346,c_23,c_8318])).

cnf(c_10922,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK3,k3_subset_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_10913])).

cnf(c_954,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_946,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
    | r1_tarski(k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)),k3_subset_1(X0,k1_xboole_0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_950,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)),k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_965,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k3_subset_1(X0,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_950,c_11])).

cnf(c_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_954])).

cnf(c_1815,plain,
    ( r1_tarski(k3_subset_1(X0,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_26,c_1662])).

cnf(c_948,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1523,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_948,c_952])).

cnf(c_1525,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1523,c_11])).

cnf(c_1821,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1815,c_1525])).

cnf(c_1825,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_951])).

cnf(c_1826,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1825,c_11])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_173,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,X1)
    | r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X2 != X0
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_173])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_388,c_13])).

cnf(c_401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3219,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1826,c_401])).

cnf(c_3227,plain,
    ( r1_tarski(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_3219])).

cnf(c_3246,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3227,c_962])).

cnf(c_3412,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_3246])).

cnf(c_1522,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_952])).

cnf(c_3421,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_3412,c_1522])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X0),X0)
    | k3_subset_1(X1,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_949,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_966,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_949,c_11])).

cnf(c_3491,plain,
    ( k3_subset_1(sK2,sK3) = sK2
    | m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3421,c_966])).

cnf(c_13327,plain,
    ( k3_subset_1(sK2,sK3) = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_3491])).

cnf(c_13611,plain,
    ( k3_subset_1(sK2,sK3) = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10922,c_13327])).

cnf(c_24,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13972,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
    | k3_subset_1(sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13611,c_24])).

cnf(c_13973,plain,
    ( k3_subset_1(sK2,sK3) = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13972])).

cnf(c_13977,plain,
    ( k3_subset_1(sK2,sK3) = sK2
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_13973])).

cnf(c_14100,plain,
    ( k3_subset_1(sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13977,c_3412])).

cnf(c_14110,plain,
    ( k3_subset_1(sK2,sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_14100,c_3421])).

cnf(c_14113,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14110,c_1525])).

cnf(c_476,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_993,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_994,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_475,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_490,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14113,c_994,c_490,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.18/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.02  
% 4.18/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.18/1.02  
% 4.18/1.02  ------  iProver source info
% 4.18/1.02  
% 4.18/1.02  git: date: 2020-06-30 10:37:57 +0100
% 4.18/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.18/1.02  git: non_committed_changes: false
% 4.18/1.02  git: last_make_outside_of_git: false
% 4.18/1.02  
% 4.18/1.02  ------ 
% 4.18/1.02  
% 4.18/1.02  ------ Input Options
% 4.18/1.02  
% 4.18/1.02  --out_options                           all
% 4.18/1.02  --tptp_safe_out                         true
% 4.18/1.02  --problem_path                          ""
% 4.18/1.02  --include_path                          ""
% 4.18/1.02  --clausifier                            res/vclausify_rel
% 4.18/1.02  --clausifier_options                    ""
% 4.18/1.02  --stdin                                 false
% 4.18/1.02  --stats_out                             all
% 4.18/1.02  
% 4.18/1.02  ------ General Options
% 4.18/1.02  
% 4.18/1.02  --fof                                   false
% 4.18/1.02  --time_out_real                         305.
% 4.18/1.02  --time_out_virtual                      -1.
% 4.18/1.02  --symbol_type_check                     false
% 4.18/1.02  --clausify_out                          false
% 4.18/1.02  --sig_cnt_out                           false
% 4.18/1.02  --trig_cnt_out                          false
% 4.18/1.02  --trig_cnt_out_tolerance                1.
% 4.18/1.02  --trig_cnt_out_sk_spl                   false
% 4.18/1.02  --abstr_cl_out                          false
% 4.18/1.02  
% 4.18/1.02  ------ Global Options
% 4.18/1.02  
% 4.18/1.02  --schedule                              default
% 4.18/1.02  --add_important_lit                     false
% 4.18/1.02  --prop_solver_per_cl                    1000
% 4.18/1.02  --min_unsat_core                        false
% 4.18/1.02  --soft_assumptions                      false
% 4.18/1.02  --soft_lemma_size                       3
% 4.18/1.02  --prop_impl_unit_size                   0
% 4.18/1.02  --prop_impl_unit                        []
% 4.18/1.02  --share_sel_clauses                     true
% 4.18/1.02  --reset_solvers                         false
% 4.18/1.02  --bc_imp_inh                            [conj_cone]
% 4.18/1.02  --conj_cone_tolerance                   3.
% 4.18/1.02  --extra_neg_conj                        none
% 4.18/1.02  --large_theory_mode                     true
% 4.18/1.02  --prolific_symb_bound                   200
% 4.18/1.02  --lt_threshold                          2000
% 4.18/1.02  --clause_weak_htbl                      true
% 4.18/1.02  --gc_record_bc_elim                     false
% 4.18/1.02  
% 4.18/1.02  ------ Preprocessing Options
% 4.18/1.02  
% 4.18/1.02  --preprocessing_flag                    true
% 4.18/1.02  --time_out_prep_mult                    0.1
% 4.18/1.02  --splitting_mode                        input
% 4.18/1.02  --splitting_grd                         true
% 4.18/1.02  --splitting_cvd                         false
% 4.18/1.02  --splitting_cvd_svl                     false
% 4.18/1.02  --splitting_nvd                         32
% 4.18/1.02  --sub_typing                            true
% 4.18/1.02  --prep_gs_sim                           true
% 4.18/1.02  --prep_unflatten                        true
% 4.18/1.02  --prep_res_sim                          true
% 4.18/1.02  --prep_upred                            true
% 4.18/1.02  --prep_sem_filter                       exhaustive
% 4.18/1.02  --prep_sem_filter_out                   false
% 4.18/1.02  --pred_elim                             true
% 4.18/1.02  --res_sim_input                         true
% 4.18/1.02  --eq_ax_congr_red                       true
% 4.18/1.02  --pure_diseq_elim                       true
% 4.18/1.02  --brand_transform                       false
% 4.18/1.02  --non_eq_to_eq                          false
% 4.18/1.02  --prep_def_merge                        true
% 4.18/1.02  --prep_def_merge_prop_impl              false
% 4.18/1.02  --prep_def_merge_mbd                    true
% 4.18/1.02  --prep_def_merge_tr_red                 false
% 4.18/1.02  --prep_def_merge_tr_cl                  false
% 4.18/1.02  --smt_preprocessing                     true
% 4.18/1.02  --smt_ac_axioms                         fast
% 4.18/1.02  --preprocessed_out                      false
% 4.18/1.02  --preprocessed_stats                    false
% 4.18/1.02  
% 4.18/1.02  ------ Abstraction refinement Options
% 4.18/1.02  
% 4.18/1.02  --abstr_ref                             []
% 4.18/1.02  --abstr_ref_prep                        false
% 4.18/1.02  --abstr_ref_until_sat                   false
% 4.18/1.02  --abstr_ref_sig_restrict                funpre
% 4.18/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.18/1.02  --abstr_ref_under                       []
% 4.18/1.02  
% 4.18/1.02  ------ SAT Options
% 4.18/1.02  
% 4.18/1.02  --sat_mode                              false
% 4.18/1.02  --sat_fm_restart_options                ""
% 4.18/1.02  --sat_gr_def                            false
% 4.18/1.02  --sat_epr_types                         true
% 4.18/1.02  --sat_non_cyclic_types                  false
% 4.18/1.02  --sat_finite_models                     false
% 4.18/1.02  --sat_fm_lemmas                         false
% 4.18/1.02  --sat_fm_prep                           false
% 4.18/1.02  --sat_fm_uc_incr                        true
% 4.18/1.02  --sat_out_model                         small
% 4.18/1.02  --sat_out_clauses                       false
% 4.18/1.02  
% 4.18/1.02  ------ QBF Options
% 4.18/1.02  
% 4.18/1.02  --qbf_mode                              false
% 4.18/1.02  --qbf_elim_univ                         false
% 4.18/1.02  --qbf_dom_inst                          none
% 4.18/1.02  --qbf_dom_pre_inst                      false
% 4.18/1.02  --qbf_sk_in                             false
% 4.18/1.02  --qbf_pred_elim                         true
% 4.18/1.02  --qbf_split                             512
% 4.18/1.02  
% 4.18/1.02  ------ BMC1 Options
% 4.18/1.02  
% 4.18/1.02  --bmc1_incremental                      false
% 4.18/1.02  --bmc1_axioms                           reachable_all
% 4.18/1.02  --bmc1_min_bound                        0
% 4.18/1.02  --bmc1_max_bound                        -1
% 4.18/1.02  --bmc1_max_bound_default                -1
% 4.18/1.02  --bmc1_symbol_reachability              true
% 4.18/1.02  --bmc1_property_lemmas                  false
% 4.18/1.02  --bmc1_k_induction                      false
% 4.18/1.02  --bmc1_non_equiv_states                 false
% 4.18/1.02  --bmc1_deadlock                         false
% 4.18/1.02  --bmc1_ucm                              false
% 4.18/1.02  --bmc1_add_unsat_core                   none
% 4.18/1.02  --bmc1_unsat_core_children              false
% 4.18/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.18/1.02  --bmc1_out_stat                         full
% 4.18/1.02  --bmc1_ground_init                      false
% 4.18/1.02  --bmc1_pre_inst_next_state              false
% 4.18/1.02  --bmc1_pre_inst_state                   false
% 4.18/1.02  --bmc1_pre_inst_reach_state             false
% 4.18/1.02  --bmc1_out_unsat_core                   false
% 4.18/1.02  --bmc1_aig_witness_out                  false
% 4.18/1.02  --bmc1_verbose                          false
% 4.18/1.02  --bmc1_dump_clauses_tptp                false
% 4.18/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.18/1.02  --bmc1_dump_file                        -
% 4.18/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.18/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.18/1.02  --bmc1_ucm_extend_mode                  1
% 4.18/1.02  --bmc1_ucm_init_mode                    2
% 4.18/1.02  --bmc1_ucm_cone_mode                    none
% 4.18/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.18/1.02  --bmc1_ucm_relax_model                  4
% 4.18/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.18/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.18/1.02  --bmc1_ucm_layered_model                none
% 4.18/1.02  --bmc1_ucm_max_lemma_size               10
% 4.18/1.02  
% 4.18/1.02  ------ AIG Options
% 4.18/1.02  
% 4.18/1.02  --aig_mode                              false
% 4.18/1.02  
% 4.18/1.02  ------ Instantiation Options
% 4.18/1.02  
% 4.18/1.02  --instantiation_flag                    true
% 4.18/1.02  --inst_sos_flag                         true
% 4.18/1.02  --inst_sos_phase                        true
% 4.18/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.18/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.18/1.02  --inst_lit_sel_side                     num_symb
% 4.18/1.02  --inst_solver_per_active                1400
% 4.18/1.02  --inst_solver_calls_frac                1.
% 4.18/1.02  --inst_passive_queue_type               priority_queues
% 4.18/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.18/1.02  --inst_passive_queues_freq              [25;2]
% 4.18/1.02  --inst_dismatching                      true
% 4.18/1.02  --inst_eager_unprocessed_to_passive     true
% 4.18/1.02  --inst_prop_sim_given                   true
% 4.18/1.02  --inst_prop_sim_new                     false
% 4.18/1.02  --inst_subs_new                         false
% 4.18/1.02  --inst_eq_res_simp                      false
% 4.18/1.02  --inst_subs_given                       false
% 4.18/1.02  --inst_orphan_elimination               true
% 4.18/1.02  --inst_learning_loop_flag               true
% 4.18/1.02  --inst_learning_start                   3000
% 4.18/1.02  --inst_learning_factor                  2
% 4.18/1.02  --inst_start_prop_sim_after_learn       3
% 4.18/1.02  --inst_sel_renew                        solver
% 4.18/1.02  --inst_lit_activity_flag                true
% 4.18/1.02  --inst_restr_to_given                   false
% 4.18/1.02  --inst_activity_threshold               500
% 4.18/1.02  --inst_out_proof                        true
% 4.18/1.02  
% 4.18/1.02  ------ Resolution Options
% 4.18/1.02  
% 4.18/1.02  --resolution_flag                       true
% 4.18/1.02  --res_lit_sel                           adaptive
% 4.18/1.02  --res_lit_sel_side                      none
% 4.18/1.02  --res_ordering                          kbo
% 4.18/1.02  --res_to_prop_solver                    active
% 4.18/1.02  --res_prop_simpl_new                    false
% 4.18/1.02  --res_prop_simpl_given                  true
% 4.18/1.02  --res_passive_queue_type                priority_queues
% 4.18/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.18/1.02  --res_passive_queues_freq               [15;5]
% 4.18/1.02  --res_forward_subs                      full
% 4.18/1.02  --res_backward_subs                     full
% 4.18/1.02  --res_forward_subs_resolution           true
% 4.18/1.02  --res_backward_subs_resolution          true
% 4.18/1.02  --res_orphan_elimination                true
% 4.18/1.02  --res_time_limit                        2.
% 4.18/1.02  --res_out_proof                         true
% 4.18/1.02  
% 4.18/1.02  ------ Superposition Options
% 4.18/1.02  
% 4.18/1.02  --superposition_flag                    true
% 4.18/1.02  --sup_passive_queue_type                priority_queues
% 4.18/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.18/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.18/1.02  --demod_completeness_check              fast
% 4.18/1.02  --demod_use_ground                      true
% 4.18/1.02  --sup_to_prop_solver                    passive
% 4.18/1.02  --sup_prop_simpl_new                    true
% 4.18/1.02  --sup_prop_simpl_given                  true
% 4.18/1.02  --sup_fun_splitting                     true
% 4.18/1.02  --sup_smt_interval                      50000
% 4.18/1.02  
% 4.18/1.02  ------ Superposition Simplification Setup
% 4.18/1.02  
% 4.18/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.18/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.18/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.18/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.18/1.02  --sup_immed_triv                        [TrivRules]
% 4.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.18/1.02  --sup_immed_bw_main                     []
% 4.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.18/1.02  --sup_input_bw                          []
% 4.18/1.02  
% 4.18/1.02  ------ Combination Options
% 4.18/1.02  
% 4.18/1.02  --comb_res_mult                         3
% 4.18/1.02  --comb_sup_mult                         2
% 4.18/1.02  --comb_inst_mult                        10
% 4.18/1.02  
% 4.18/1.02  ------ Debug Options
% 4.18/1.02  
% 4.18/1.02  --dbg_backtrace                         false
% 4.18/1.02  --dbg_dump_prop_clauses                 false
% 4.18/1.02  --dbg_dump_prop_clauses_file            -
% 4.18/1.02  --dbg_out_stat                          false
% 4.18/1.02  ------ Parsing...
% 4.18/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.18/1.02  
% 4.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.18/1.02  
% 4.18/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.18/1.02  
% 4.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.18/1.02  ------ Proving...
% 4.18/1.02  ------ Problem Properties 
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  clauses                                 23
% 4.18/1.02  conjectures                             4
% 4.18/1.02  EPR                                     8
% 4.18/1.02  Horn                                    20
% 4.18/1.02  unary                                   7
% 4.18/1.02  binary                                  8
% 4.18/1.02  lits                                    48
% 4.18/1.02  lits eq                                 6
% 4.18/1.02  fd_pure                                 0
% 4.18/1.02  fd_pseudo                               0
% 4.18/1.02  fd_cond                                 0
% 4.18/1.02  fd_pseudo_cond                          3
% 4.18/1.02  AC symbols                              0
% 4.18/1.02  
% 4.18/1.02  ------ Schedule dynamic 5 is on 
% 4.18/1.02  
% 4.18/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  ------ 
% 4.18/1.02  Current options:
% 4.18/1.02  ------ 
% 4.18/1.02  
% 4.18/1.02  ------ Input Options
% 4.18/1.02  
% 4.18/1.02  --out_options                           all
% 4.18/1.02  --tptp_safe_out                         true
% 4.18/1.02  --problem_path                          ""
% 4.18/1.02  --include_path                          ""
% 4.18/1.02  --clausifier                            res/vclausify_rel
% 4.18/1.02  --clausifier_options                    ""
% 4.18/1.02  --stdin                                 false
% 4.18/1.02  --stats_out                             all
% 4.18/1.02  
% 4.18/1.02  ------ General Options
% 4.18/1.02  
% 4.18/1.02  --fof                                   false
% 4.18/1.02  --time_out_real                         305.
% 4.18/1.02  --time_out_virtual                      -1.
% 4.18/1.02  --symbol_type_check                     false
% 4.18/1.02  --clausify_out                          false
% 4.18/1.02  --sig_cnt_out                           false
% 4.18/1.02  --trig_cnt_out                          false
% 4.18/1.02  --trig_cnt_out_tolerance                1.
% 4.18/1.02  --trig_cnt_out_sk_spl                   false
% 4.18/1.02  --abstr_cl_out                          false
% 4.18/1.02  
% 4.18/1.02  ------ Global Options
% 4.18/1.02  
% 4.18/1.02  --schedule                              default
% 4.18/1.02  --add_important_lit                     false
% 4.18/1.02  --prop_solver_per_cl                    1000
% 4.18/1.02  --min_unsat_core                        false
% 4.18/1.02  --soft_assumptions                      false
% 4.18/1.02  --soft_lemma_size                       3
% 4.18/1.02  --prop_impl_unit_size                   0
% 4.18/1.02  --prop_impl_unit                        []
% 4.18/1.02  --share_sel_clauses                     true
% 4.18/1.02  --reset_solvers                         false
% 4.18/1.02  --bc_imp_inh                            [conj_cone]
% 4.18/1.02  --conj_cone_tolerance                   3.
% 4.18/1.02  --extra_neg_conj                        none
% 4.18/1.02  --large_theory_mode                     true
% 4.18/1.02  --prolific_symb_bound                   200
% 4.18/1.02  --lt_threshold                          2000
% 4.18/1.02  --clause_weak_htbl                      true
% 4.18/1.02  --gc_record_bc_elim                     false
% 4.18/1.02  
% 4.18/1.02  ------ Preprocessing Options
% 4.18/1.02  
% 4.18/1.02  --preprocessing_flag                    true
% 4.18/1.02  --time_out_prep_mult                    0.1
% 4.18/1.02  --splitting_mode                        input
% 4.18/1.02  --splitting_grd                         true
% 4.18/1.02  --splitting_cvd                         false
% 4.18/1.02  --splitting_cvd_svl                     false
% 4.18/1.02  --splitting_nvd                         32
% 4.18/1.02  --sub_typing                            true
% 4.18/1.02  --prep_gs_sim                           true
% 4.18/1.02  --prep_unflatten                        true
% 4.18/1.02  --prep_res_sim                          true
% 4.18/1.02  --prep_upred                            true
% 4.18/1.02  --prep_sem_filter                       exhaustive
% 4.18/1.02  --prep_sem_filter_out                   false
% 4.18/1.02  --pred_elim                             true
% 4.18/1.02  --res_sim_input                         true
% 4.18/1.02  --eq_ax_congr_red                       true
% 4.18/1.02  --pure_diseq_elim                       true
% 4.18/1.02  --brand_transform                       false
% 4.18/1.02  --non_eq_to_eq                          false
% 4.18/1.02  --prep_def_merge                        true
% 4.18/1.02  --prep_def_merge_prop_impl              false
% 4.18/1.02  --prep_def_merge_mbd                    true
% 4.18/1.02  --prep_def_merge_tr_red                 false
% 4.18/1.02  --prep_def_merge_tr_cl                  false
% 4.18/1.02  --smt_preprocessing                     true
% 4.18/1.02  --smt_ac_axioms                         fast
% 4.18/1.02  --preprocessed_out                      false
% 4.18/1.02  --preprocessed_stats                    false
% 4.18/1.02  
% 4.18/1.02  ------ Abstraction refinement Options
% 4.18/1.02  
% 4.18/1.02  --abstr_ref                             []
% 4.18/1.02  --abstr_ref_prep                        false
% 4.18/1.02  --abstr_ref_until_sat                   false
% 4.18/1.02  --abstr_ref_sig_restrict                funpre
% 4.18/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.18/1.02  --abstr_ref_under                       []
% 4.18/1.02  
% 4.18/1.02  ------ SAT Options
% 4.18/1.02  
% 4.18/1.02  --sat_mode                              false
% 4.18/1.02  --sat_fm_restart_options                ""
% 4.18/1.02  --sat_gr_def                            false
% 4.18/1.02  --sat_epr_types                         true
% 4.18/1.02  --sat_non_cyclic_types                  false
% 4.18/1.02  --sat_finite_models                     false
% 4.18/1.02  --sat_fm_lemmas                         false
% 4.18/1.02  --sat_fm_prep                           false
% 4.18/1.02  --sat_fm_uc_incr                        true
% 4.18/1.02  --sat_out_model                         small
% 4.18/1.02  --sat_out_clauses                       false
% 4.18/1.02  
% 4.18/1.02  ------ QBF Options
% 4.18/1.02  
% 4.18/1.02  --qbf_mode                              false
% 4.18/1.02  --qbf_elim_univ                         false
% 4.18/1.02  --qbf_dom_inst                          none
% 4.18/1.02  --qbf_dom_pre_inst                      false
% 4.18/1.02  --qbf_sk_in                             false
% 4.18/1.02  --qbf_pred_elim                         true
% 4.18/1.02  --qbf_split                             512
% 4.18/1.02  
% 4.18/1.02  ------ BMC1 Options
% 4.18/1.02  
% 4.18/1.02  --bmc1_incremental                      false
% 4.18/1.02  --bmc1_axioms                           reachable_all
% 4.18/1.02  --bmc1_min_bound                        0
% 4.18/1.02  --bmc1_max_bound                        -1
% 4.18/1.02  --bmc1_max_bound_default                -1
% 4.18/1.02  --bmc1_symbol_reachability              true
% 4.18/1.02  --bmc1_property_lemmas                  false
% 4.18/1.02  --bmc1_k_induction                      false
% 4.18/1.02  --bmc1_non_equiv_states                 false
% 4.18/1.02  --bmc1_deadlock                         false
% 4.18/1.02  --bmc1_ucm                              false
% 4.18/1.02  --bmc1_add_unsat_core                   none
% 4.18/1.02  --bmc1_unsat_core_children              false
% 4.18/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.18/1.02  --bmc1_out_stat                         full
% 4.18/1.02  --bmc1_ground_init                      false
% 4.18/1.02  --bmc1_pre_inst_next_state              false
% 4.18/1.02  --bmc1_pre_inst_state                   false
% 4.18/1.02  --bmc1_pre_inst_reach_state             false
% 4.18/1.02  --bmc1_out_unsat_core                   false
% 4.18/1.02  --bmc1_aig_witness_out                  false
% 4.18/1.02  --bmc1_verbose                          false
% 4.18/1.02  --bmc1_dump_clauses_tptp                false
% 4.18/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.18/1.02  --bmc1_dump_file                        -
% 4.18/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.18/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.18/1.02  --bmc1_ucm_extend_mode                  1
% 4.18/1.02  --bmc1_ucm_init_mode                    2
% 4.18/1.02  --bmc1_ucm_cone_mode                    none
% 4.18/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.18/1.02  --bmc1_ucm_relax_model                  4
% 4.18/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.18/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.18/1.02  --bmc1_ucm_layered_model                none
% 4.18/1.02  --bmc1_ucm_max_lemma_size               10
% 4.18/1.02  
% 4.18/1.02  ------ AIG Options
% 4.18/1.02  
% 4.18/1.02  --aig_mode                              false
% 4.18/1.02  
% 4.18/1.02  ------ Instantiation Options
% 4.18/1.02  
% 4.18/1.02  --instantiation_flag                    true
% 4.18/1.02  --inst_sos_flag                         true
% 4.18/1.02  --inst_sos_phase                        true
% 4.18/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.18/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.18/1.02  --inst_lit_sel_side                     none
% 4.18/1.02  --inst_solver_per_active                1400
% 4.18/1.02  --inst_solver_calls_frac                1.
% 4.18/1.02  --inst_passive_queue_type               priority_queues
% 4.18/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.18/1.02  --inst_passive_queues_freq              [25;2]
% 4.18/1.02  --inst_dismatching                      true
% 4.18/1.02  --inst_eager_unprocessed_to_passive     true
% 4.18/1.02  --inst_prop_sim_given                   true
% 4.18/1.02  --inst_prop_sim_new                     false
% 4.18/1.02  --inst_subs_new                         false
% 4.18/1.02  --inst_eq_res_simp                      false
% 4.18/1.02  --inst_subs_given                       false
% 4.18/1.02  --inst_orphan_elimination               true
% 4.18/1.02  --inst_learning_loop_flag               true
% 4.18/1.02  --inst_learning_start                   3000
% 4.18/1.02  --inst_learning_factor                  2
% 4.18/1.02  --inst_start_prop_sim_after_learn       3
% 4.18/1.02  --inst_sel_renew                        solver
% 4.18/1.02  --inst_lit_activity_flag                true
% 4.18/1.02  --inst_restr_to_given                   false
% 4.18/1.02  --inst_activity_threshold               500
% 4.18/1.02  --inst_out_proof                        true
% 4.18/1.02  
% 4.18/1.02  ------ Resolution Options
% 4.18/1.02  
% 4.18/1.02  --resolution_flag                       false
% 4.18/1.02  --res_lit_sel                           adaptive
% 4.18/1.02  --res_lit_sel_side                      none
% 4.18/1.02  --res_ordering                          kbo
% 4.18/1.02  --res_to_prop_solver                    active
% 4.18/1.02  --res_prop_simpl_new                    false
% 4.18/1.02  --res_prop_simpl_given                  true
% 4.18/1.02  --res_passive_queue_type                priority_queues
% 4.18/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.18/1.02  --res_passive_queues_freq               [15;5]
% 4.18/1.02  --res_forward_subs                      full
% 4.18/1.02  --res_backward_subs                     full
% 4.18/1.02  --res_forward_subs_resolution           true
% 4.18/1.02  --res_backward_subs_resolution          true
% 4.18/1.02  --res_orphan_elimination                true
% 4.18/1.02  --res_time_limit                        2.
% 4.18/1.02  --res_out_proof                         true
% 4.18/1.02  
% 4.18/1.02  ------ Superposition Options
% 4.18/1.02  
% 4.18/1.02  --superposition_flag                    true
% 4.18/1.02  --sup_passive_queue_type                priority_queues
% 4.18/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.18/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.18/1.02  --demod_completeness_check              fast
% 4.18/1.02  --demod_use_ground                      true
% 4.18/1.02  --sup_to_prop_solver                    passive
% 4.18/1.02  --sup_prop_simpl_new                    true
% 4.18/1.02  --sup_prop_simpl_given                  true
% 4.18/1.02  --sup_fun_splitting                     true
% 4.18/1.02  --sup_smt_interval                      50000
% 4.18/1.02  
% 4.18/1.02  ------ Superposition Simplification Setup
% 4.18/1.02  
% 4.18/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.18/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.18/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.18/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.18/1.02  --sup_immed_triv                        [TrivRules]
% 4.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.18/1.02  --sup_immed_bw_main                     []
% 4.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.18/1.02  --sup_input_bw                          []
% 4.18/1.02  
% 4.18/1.02  ------ Combination Options
% 4.18/1.02  
% 4.18/1.02  --comb_res_mult                         3
% 4.18/1.02  --comb_sup_mult                         2
% 4.18/1.02  --comb_inst_mult                        10
% 4.18/1.02  
% 4.18/1.02  ------ Debug Options
% 4.18/1.02  
% 4.18/1.02  --dbg_backtrace                         false
% 4.18/1.02  --dbg_dump_prop_clauses                 false
% 4.18/1.02  --dbg_dump_prop_clauses_file            -
% 4.18/1.02  --dbg_out_stat                          false
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  ------ Proving...
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  % SZS status Theorem for theBenchmark.p
% 4.18/1.02  
% 4.18/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 4.18/1.02  
% 4.18/1.02  fof(f3,axiom,(
% 4.18/1.02    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f30,plain,(
% 4.18/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.18/1.02    inference(nnf_transformation,[],[f3])).
% 4.18/1.02  
% 4.18/1.02  fof(f31,plain,(
% 4.18/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.18/1.02    inference(rectify,[],[f30])).
% 4.18/1.02  
% 4.18/1.02  fof(f32,plain,(
% 4.18/1.02    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 4.18/1.02    introduced(choice_axiom,[])).
% 4.18/1.02  
% 4.18/1.02  fof(f33,plain,(
% 4.18/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 4.18/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 4.18/1.02  
% 4.18/1.02  fof(f42,plain,(
% 4.18/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 4.18/1.02    inference(cnf_transformation,[],[f33])).
% 4.18/1.02  
% 4.18/1.02  fof(f67,plain,(
% 4.18/1.02    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 4.18/1.02    inference(equality_resolution,[],[f42])).
% 4.18/1.02  
% 4.18/1.02  fof(f4,axiom,(
% 4.18/1.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f18,plain,(
% 4.18/1.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.18/1.02    inference(ennf_transformation,[],[f4])).
% 4.18/1.02  
% 4.18/1.02  fof(f34,plain,(
% 4.18/1.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 4.18/1.02    inference(nnf_transformation,[],[f18])).
% 4.18/1.02  
% 4.18/1.02  fof(f46,plain,(
% 4.18/1.02    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.18/1.02    inference(cnf_transformation,[],[f34])).
% 4.18/1.02  
% 4.18/1.02  fof(f1,axiom,(
% 4.18/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f26,plain,(
% 4.18/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.18/1.02    inference(nnf_transformation,[],[f1])).
% 4.18/1.02  
% 4.18/1.02  fof(f27,plain,(
% 4.18/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.18/1.02    inference(rectify,[],[f26])).
% 4.18/1.02  
% 4.18/1.02  fof(f28,plain,(
% 4.18/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 4.18/1.02    introduced(choice_axiom,[])).
% 4.18/1.02  
% 4.18/1.02  fof(f29,plain,(
% 4.18/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.18/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 4.18/1.02  
% 4.18/1.02  fof(f38,plain,(
% 4.18/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.18/1.02    inference(cnf_transformation,[],[f29])).
% 4.18/1.02  
% 4.18/1.02  fof(f14,conjecture,(
% 4.18/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f15,negated_conjecture,(
% 4.18/1.02    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 4.18/1.02    inference(negated_conjecture,[],[f14])).
% 4.18/1.02  
% 4.18/1.02  fof(f24,plain,(
% 4.18/1.02    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(ennf_transformation,[],[f15])).
% 4.18/1.02  
% 4.18/1.02  fof(f25,plain,(
% 4.18/1.02    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(flattening,[],[f24])).
% 4.18/1.02  
% 4.18/1.02  fof(f36,plain,(
% 4.18/1.02    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK3 & r1_tarski(sK3,k3_subset_1(sK2,sK4)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK2)))),
% 4.18/1.02    introduced(choice_axiom,[])).
% 4.18/1.02  
% 4.18/1.02  fof(f37,plain,(
% 4.18/1.02    k1_xboole_0 != sK3 & r1_tarski(sK3,k3_subset_1(sK2,sK4)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 4.18/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f36])).
% 4.18/1.02  
% 4.18/1.02  fof(f61,plain,(
% 4.18/1.02    r1_tarski(sK3,k3_subset_1(sK2,sK4))),
% 4.18/1.02    inference(cnf_transformation,[],[f37])).
% 4.18/1.02  
% 4.18/1.02  fof(f59,plain,(
% 4.18/1.02    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 4.18/1.02    inference(cnf_transformation,[],[f37])).
% 4.18/1.02  
% 4.18/1.02  fof(f9,axiom,(
% 4.18/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f20,plain,(
% 4.18/1.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(ennf_transformation,[],[f9])).
% 4.18/1.02  
% 4.18/1.02  fof(f53,plain,(
% 4.18/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f20])).
% 4.18/1.02  
% 4.18/1.02  fof(f11,axiom,(
% 4.18/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f21,plain,(
% 4.18/1.02    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(ennf_transformation,[],[f11])).
% 4.18/1.02  
% 4.18/1.02  fof(f22,plain,(
% 4.18/1.02    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(flattening,[],[f21])).
% 4.18/1.02  
% 4.18/1.02  fof(f55,plain,(
% 4.18/1.02    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f22])).
% 4.18/1.02  
% 4.18/1.02  fof(f2,axiom,(
% 4.18/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f16,plain,(
% 4.18/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.18/1.02    inference(ennf_transformation,[],[f2])).
% 4.18/1.02  
% 4.18/1.02  fof(f17,plain,(
% 4.18/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.18/1.02    inference(flattening,[],[f16])).
% 4.18/1.02  
% 4.18/1.02  fof(f40,plain,(
% 4.18/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.18/1.02    inference(cnf_transformation,[],[f17])).
% 4.18/1.02  
% 4.18/1.02  fof(f7,axiom,(
% 4.18/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f19,plain,(
% 4.18/1.02    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(ennf_transformation,[],[f7])).
% 4.18/1.02  
% 4.18/1.02  fof(f51,plain,(
% 4.18/1.02    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f19])).
% 4.18/1.02  
% 4.18/1.02  fof(f60,plain,(
% 4.18/1.02    r1_tarski(sK3,sK4)),
% 4.18/1.02    inference(cnf_transformation,[],[f37])).
% 4.18/1.02  
% 4.18/1.02  fof(f12,axiom,(
% 4.18/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f23,plain,(
% 4.18/1.02    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(ennf_transformation,[],[f12])).
% 4.18/1.02  
% 4.18/1.02  fof(f35,plain,(
% 4.18/1.02    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.18/1.02    inference(nnf_transformation,[],[f23])).
% 4.18/1.02  
% 4.18/1.02  fof(f57,plain,(
% 4.18/1.02    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f35])).
% 4.18/1.02  
% 4.18/1.02  fof(f10,axiom,(
% 4.18/1.02    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f54,plain,(
% 4.18/1.02    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f10])).
% 4.18/1.02  
% 4.18/1.02  fof(f5,axiom,(
% 4.18/1.02    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f49,plain,(
% 4.18/1.02    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 4.18/1.02    inference(cnf_transformation,[],[f5])).
% 4.18/1.02  
% 4.18/1.02  fof(f63,plain,(
% 4.18/1.02    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 4.18/1.02    inference(definition_unfolding,[],[f54,f49])).
% 4.18/1.02  
% 4.18/1.02  fof(f65,plain,(
% 4.18/1.02    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X1) | k3_subset_1(X0,k1_xboole_0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(definition_unfolding,[],[f57,f63])).
% 4.18/1.02  
% 4.18/1.02  fof(f69,plain,(
% 4.18/1.02    ( ! [X0] : (r1_tarski(k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)),k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(equality_resolution,[],[f65])).
% 4.18/1.02  
% 4.18/1.02  fof(f6,axiom,(
% 4.18/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f50,plain,(
% 4.18/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.18/1.02    inference(cnf_transformation,[],[f6])).
% 4.18/1.02  
% 4.18/1.02  fof(f64,plain,(
% 4.18/1.02    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 4.18/1.02    inference(definition_unfolding,[],[f50,f63])).
% 4.18/1.02  
% 4.18/1.02  fof(f13,axiom,(
% 4.18/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f58,plain,(
% 4.18/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f13])).
% 4.18/1.02  
% 4.18/1.02  fof(f45,plain,(
% 4.18/1.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 4.18/1.02    inference(cnf_transformation,[],[f34])).
% 4.18/1.02  
% 4.18/1.02  fof(f41,plain,(
% 4.18/1.02    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 4.18/1.02    inference(cnf_transformation,[],[f33])).
% 4.18/1.02  
% 4.18/1.02  fof(f68,plain,(
% 4.18/1.02    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(equality_resolution,[],[f41])).
% 4.18/1.02  
% 4.18/1.02  fof(f8,axiom,(
% 4.18/1.02    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 4.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.18/1.02  
% 4.18/1.02  fof(f52,plain,(
% 4.18/1.02    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f8])).
% 4.18/1.02  
% 4.18/1.02  fof(f56,plain,(
% 4.18/1.02    ( ! [X0,X1] : (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(cnf_transformation,[],[f35])).
% 4.18/1.02  
% 4.18/1.02  fof(f66,plain,(
% 4.18/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k1_xboole_0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.18/1.02    inference(definition_unfolding,[],[f56,f63])).
% 4.18/1.02  
% 4.18/1.02  fof(f62,plain,(
% 4.18/1.02    k1_xboole_0 != sK3),
% 4.18/1.02    inference(cnf_transformation,[],[f37])).
% 4.18/1.02  
% 4.18/1.02  cnf(c_5,plain,
% 4.18/1.02      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f67]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_959,plain,
% 4.18/1.02      ( r1_tarski(X0,X1) != iProver_top
% 4.18/1.02      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_9,plain,
% 4.18/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.18/1.02      inference(cnf_transformation,[],[f46]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1,plain,
% 4.18/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.18/1.02      inference(cnf_transformation,[],[f38]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_129,plain,
% 4.18/1.02      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 4.18/1.02      inference(global_propositional_subsumption,[status(thm)],[c_9,c_1]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_130,plain,
% 4.18/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 4.18/1.02      inference(renaming,[status(thm)],[c_129]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_944,plain,
% 4.18/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 4.18/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_130]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1441,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.18/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_959,c_944]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_20,negated_conjecture,
% 4.18/1.02      ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f61]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_947,plain,
% 4.18/1.02      ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_22,negated_conjecture,
% 4.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f59]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_945,plain,
% 4.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_14,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 4.18/1.02      inference(cnf_transformation,[],[f53]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_952,plain,
% 4.18/1.02      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 4.18/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1524,plain,
% 4.18/1.02      ( k3_subset_1(sK2,k3_subset_1(sK2,sK4)) = sK4 ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_945,c_952]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_15,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.18/1.02      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 4.18/1.02      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f55]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_951,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
% 4.18/1.02      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1604,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,sK4) != iProver_top
% 4.18/1.02      | r1_tarski(k3_subset_1(sK2,sK4),k3_subset_1(sK2,X0)) = iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_1524,c_951]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_2,plain,
% 4.18/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 4.18/1.02      inference(cnf_transformation,[],[f40]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_962,plain,
% 4.18/1.02      ( r1_tarski(X0,X1) != iProver_top
% 4.18/1.02      | r1_tarski(X2,X0) != iProver_top
% 4.18/1.02      | r1_tarski(X2,X1) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_2346,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | r1_tarski(X1,k3_subset_1(sK2,X0)) = iProver_top
% 4.18/1.02      | r1_tarski(X1,k3_subset_1(sK2,sK4)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,sK4) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_1604,c_962]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_23,plain,
% 4.18/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_12,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f51]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_8317,plain,
% 4.18/1.02      ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2))
% 4.18/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 4.18/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_8318,plain,
% 4.18/1.02      ( m1_subset_1(k3_subset_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
% 4.18/1.02      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_8317]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_10913,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | r1_tarski(X1,k3_subset_1(sK2,X0)) = iProver_top
% 4.18/1.02      | r1_tarski(X1,k3_subset_1(sK2,sK4)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,sK4) != iProver_top ),
% 4.18/1.02      inference(global_propositional_subsumption,
% 4.18/1.02                [status(thm)],
% 4.18/1.02                [c_2346,c_23,c_8318]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_10922,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,sK4) != iProver_top
% 4.18/1.02      | r1_tarski(sK3,k3_subset_1(sK2,X0)) = iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_947,c_10913]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_954,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_21,negated_conjecture,
% 4.18/1.02      ( r1_tarski(sK3,sK4) ),
% 4.18/1.02      inference(cnf_transformation,[],[f60]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_946,plain,
% 4.18/1.02      ( r1_tarski(sK3,sK4) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_16,plain,
% 4.18/1.02      ( ~ m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
% 4.18/1.02      | r1_tarski(k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)),k3_subset_1(X0,k1_xboole_0)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f69]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_950,plain,
% 4.18/1.02      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
% 4.18/1.02      | r1_tarski(k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)),k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_11,plain,
% 4.18/1.02      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 4.18/1.02      inference(cnf_transformation,[],[f64]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_965,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 4.18/1.02      | r1_tarski(k3_subset_1(X0,X0),X0) = iProver_top ),
% 4.18/1.02      inference(light_normalisation,[status(thm)],[c_950,c_11]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_18,plain,
% 4.18/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f58]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_26,plain,
% 4.18/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1662,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 4.18/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_11,c_954]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1815,plain,
% 4.18/1.02      ( r1_tarski(k3_subset_1(X0,X0),X0) = iProver_top ),
% 4.18/1.02      inference(global_propositional_subsumption,
% 4.18/1.02                [status(thm)],
% 4.18/1.02                [c_965,c_26,c_1662]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_948,plain,
% 4.18/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1523,plain,
% 4.18/1.02      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_948,c_952]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1525,plain,
% 4.18/1.02      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 4.18/1.02      inference(light_normalisation,[status(thm)],[c_1523,c_11]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1821,plain,
% 4.18/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.18/1.02      inference(light_normalisation,[status(thm)],[c_1815,c_1525]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1825,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_1821,c_951]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1826,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 4.18/1.02      inference(demodulation,[status(thm)],[c_1825,c_11]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_10,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.18/1.02      inference(cnf_transformation,[],[f45]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_6,plain,
% 4.18/1.02      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f68]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_173,plain,
% 4.18/1.02      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 4.18/1.02      inference(prop_impl,[status(thm)],[c_6]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_387,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,X1)
% 4.18/1.02      | r1_tarski(X2,X3)
% 4.18/1.02      | v1_xboole_0(X1)
% 4.18/1.02      | X2 != X0
% 4.18/1.02      | k1_zfmisc_1(X3) != X1 ),
% 4.18/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_173]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_388,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.02      | r1_tarski(X0,X1)
% 4.18/1.02      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 4.18/1.02      inference(unflattening,[status(thm)],[c_387]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_13,plain,
% 4.18/1.02      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 4.18/1.02      inference(cnf_transformation,[],[f52]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_398,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.18/1.02      inference(forward_subsumption_resolution,
% 4.18/1.02                [status(thm)],
% 4.18/1.02                [c_388,c_13]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_401,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_3219,plain,
% 4.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 4.18/1.02      inference(global_propositional_subsumption,
% 4.18/1.02                [status(thm)],
% 4.18/1.02                [c_1826,c_401]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_3227,plain,
% 4.18/1.02      ( r1_tarski(sK4,sK2) = iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_945,c_3219]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_3246,plain,
% 4.18/1.02      ( r1_tarski(X0,sK4) != iProver_top
% 4.18/1.02      | r1_tarski(X0,sK2) = iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_3227,c_962]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_3412,plain,
% 4.18/1.02      ( r1_tarski(sK3,sK2) = iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_946,c_3246]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_1522,plain,
% 4.18/1.02      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 4.18/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_1441,c_952]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_3421,plain,
% 4.18/1.02      ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_3412,c_1522]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_17,plain,
% 4.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.18/1.02      | ~ r1_tarski(k3_subset_1(X1,X0),X0)
% 4.18/1.02      | k3_subset_1(X1,k1_xboole_0) = X0 ),
% 4.18/1.02      inference(cnf_transformation,[],[f66]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_949,plain,
% 4.18/1.02      ( k3_subset_1(X0,k1_xboole_0) = X1
% 4.18/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 4.18/1.02      | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_966,plain,
% 4.18/1.02      ( X0 = X1
% 4.18/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.18/1.02      | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top ),
% 4.18/1.02      inference(demodulation,[status(thm)],[c_949,c_11]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_3491,plain,
% 4.18/1.02      ( k3_subset_1(sK2,sK3) = sK2
% 4.18/1.02      | m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | r1_tarski(sK3,k3_subset_1(sK2,sK3)) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_3421,c_966]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_13327,plain,
% 4.18/1.02      ( k3_subset_1(sK2,sK3) = sK2
% 4.18/1.02      | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | r1_tarski(sK3,k3_subset_1(sK2,sK3)) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_954,c_3491]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_13611,plain,
% 4.18/1.02      ( k3_subset_1(sK2,sK3) = sK2
% 4.18/1.02      | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | r1_tarski(sK3,sK4) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_10922,c_13327]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_24,plain,
% 4.18/1.02      ( r1_tarski(sK3,sK4) = iProver_top ),
% 4.18/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_13972,plain,
% 4.18/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top
% 4.18/1.02      | k3_subset_1(sK2,sK3) = sK2 ),
% 4.18/1.02      inference(global_propositional_subsumption,
% 4.18/1.02                [status(thm)],
% 4.18/1.02                [c_13611,c_24]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_13973,plain,
% 4.18/1.02      ( k3_subset_1(sK2,sK3) = sK2
% 4.18/1.02      | m1_subset_1(sK3,k1_zfmisc_1(sK2)) != iProver_top ),
% 4.18/1.02      inference(renaming,[status(thm)],[c_13972]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_13977,plain,
% 4.18/1.02      ( k3_subset_1(sK2,sK3) = sK2 | r1_tarski(sK3,sK2) != iProver_top ),
% 4.18/1.02      inference(superposition,[status(thm)],[c_1441,c_13973]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_14100,plain,
% 4.18/1.02      ( k3_subset_1(sK2,sK3) = sK2 ),
% 4.18/1.02      inference(global_propositional_subsumption,
% 4.18/1.02                [status(thm)],
% 4.18/1.02                [c_13977,c_3412]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_14110,plain,
% 4.18/1.02      ( k3_subset_1(sK2,sK2) = sK3 ),
% 4.18/1.02      inference(demodulation,[status(thm)],[c_14100,c_3421]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_14113,plain,
% 4.18/1.02      ( sK3 = k1_xboole_0 ),
% 4.18/1.02      inference(demodulation,[status(thm)],[c_14110,c_1525]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_476,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_993,plain,
% 4.18/1.02      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 4.18/1.02      inference(instantiation,[status(thm)],[c_476]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_994,plain,
% 4.18/1.02      ( sK3 != k1_xboole_0
% 4.18/1.02      | k1_xboole_0 = sK3
% 4.18/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 4.18/1.02      inference(instantiation,[status(thm)],[c_993]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_475,plain,( X0 = X0 ),theory(equality) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_490,plain,
% 4.18/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 4.18/1.02      inference(instantiation,[status(thm)],[c_475]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(c_19,negated_conjecture,
% 4.18/1.02      ( k1_xboole_0 != sK3 ),
% 4.18/1.02      inference(cnf_transformation,[],[f62]) ).
% 4.18/1.02  
% 4.18/1.02  cnf(contradiction,plain,
% 4.18/1.02      ( $false ),
% 4.18/1.02      inference(minisat,[status(thm)],[c_14113,c_994,c_490,c_19]) ).
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 4.18/1.02  
% 4.18/1.02  ------                               Statistics
% 4.18/1.02  
% 4.18/1.02  ------ General
% 4.18/1.02  
% 4.18/1.02  abstr_ref_over_cycles:                  0
% 4.18/1.02  abstr_ref_under_cycles:                 0
% 4.18/1.02  gc_basic_clause_elim:                   0
% 4.18/1.02  forced_gc_time:                         0
% 4.18/1.02  parsing_time:                           0.028
% 4.18/1.02  unif_index_cands_time:                  0.
% 4.18/1.02  unif_index_add_time:                    0.
% 4.18/1.02  orderings_time:                         0.
% 4.18/1.02  out_proof_time:                         0.012
% 4.18/1.02  total_time:                             0.461
% 4.18/1.02  num_of_symbols:                         43
% 4.18/1.02  num_of_terms:                           11873
% 4.18/1.02  
% 4.18/1.02  ------ Preprocessing
% 4.18/1.02  
% 4.18/1.02  num_of_splits:                          0
% 4.18/1.02  num_of_split_atoms:                     0
% 4.18/1.02  num_of_reused_defs:                     0
% 4.18/1.02  num_eq_ax_congr_red:                    6
% 4.18/1.02  num_of_sem_filtered_clauses:            1
% 4.18/1.02  num_of_subtypes:                        0
% 4.18/1.02  monotx_restored_types:                  0
% 4.18/1.02  sat_num_of_epr_types:                   0
% 4.18/1.02  sat_num_of_non_cyclic_types:            0
% 4.18/1.02  sat_guarded_non_collapsed_types:        0
% 4.18/1.02  num_pure_diseq_elim:                    0
% 4.18/1.02  simp_replaced_by:                       0
% 4.18/1.02  res_preprocessed:                       86
% 4.18/1.02  prep_upred:                             0
% 4.18/1.02  prep_unflattend:                        23
% 4.18/1.02  smt_new_axioms:                         0
% 4.18/1.02  pred_elim_cands:                        4
% 4.18/1.02  pred_elim:                              0
% 4.18/1.02  pred_elim_cl:                           0
% 4.18/1.02  pred_elim_cycles:                       1
% 4.18/1.02  merged_defs:                            6
% 4.18/1.02  merged_defs_ncl:                        0
% 4.18/1.02  bin_hyper_res:                          6
% 4.18/1.02  prep_cycles:                            3
% 4.18/1.02  pred_elim_time:                         0.001
% 4.18/1.02  splitting_time:                         0.
% 4.18/1.02  sem_filter_time:                        0.
% 4.18/1.02  monotx_time:                            0.
% 4.18/1.02  subtype_inf_time:                       0.
% 4.18/1.02  
% 4.18/1.02  ------ Problem properties
% 4.18/1.02  
% 4.18/1.02  clauses:                                23
% 4.18/1.02  conjectures:                            4
% 4.18/1.02  epr:                                    8
% 4.18/1.02  horn:                                   20
% 4.18/1.02  ground:                                 4
% 4.18/1.02  unary:                                  7
% 4.18/1.02  binary:                                 8
% 4.18/1.02  lits:                                   48
% 4.18/1.02  lits_eq:                                6
% 4.18/1.02  fd_pure:                                0
% 4.18/1.02  fd_pseudo:                              0
% 4.18/1.02  fd_cond:                                0
% 4.18/1.02  fd_pseudo_cond:                         3
% 4.18/1.02  ac_symbols:                             0
% 4.18/1.02  
% 4.18/1.02  ------ Propositional Solver
% 4.18/1.02  
% 4.18/1.02  prop_solver_calls:                      31
% 4.18/1.02  prop_fast_solver_calls:                 967
% 4.18/1.02  smt_solver_calls:                       0
% 4.18/1.02  smt_fast_solver_calls:                  0
% 4.18/1.02  prop_num_of_clauses:                    6714
% 4.18/1.02  prop_preprocess_simplified:             10995
% 4.18/1.02  prop_fo_subsumed:                       61
% 4.18/1.02  prop_solver_time:                       0.
% 4.18/1.02  smt_solver_time:                        0.
% 4.18/1.02  smt_fast_solver_time:                   0.
% 4.18/1.02  prop_fast_solver_time:                  0.
% 4.18/1.02  prop_unsat_core_time:                   0.
% 4.18/1.02  
% 4.18/1.02  ------ QBF
% 4.18/1.02  
% 4.18/1.02  qbf_q_res:                              0
% 4.18/1.02  qbf_num_tautologies:                    0
% 4.18/1.02  qbf_prep_cycles:                        0
% 4.18/1.02  
% 4.18/1.02  ------ BMC1
% 4.18/1.02  
% 4.18/1.02  bmc1_current_bound:                     -1
% 4.18/1.02  bmc1_last_solved_bound:                 -1
% 4.18/1.02  bmc1_unsat_core_size:                   -1
% 4.18/1.02  bmc1_unsat_core_parents_size:           -1
% 4.18/1.02  bmc1_merge_next_fun:                    0
% 4.18/1.02  bmc1_unsat_core_clauses_time:           0.
% 4.18/1.02  
% 4.18/1.02  ------ Instantiation
% 4.18/1.02  
% 4.18/1.02  inst_num_of_clauses:                    1999
% 4.18/1.02  inst_num_in_passive:                    255
% 4.18/1.02  inst_num_in_active:                     747
% 4.18/1.02  inst_num_in_unprocessed:                998
% 4.18/1.02  inst_num_of_loops:                      840
% 4.18/1.02  inst_num_of_learning_restarts:          0
% 4.18/1.02  inst_num_moves_active_passive:          85
% 4.18/1.02  inst_lit_activity:                      0
% 4.18/1.02  inst_lit_activity_moves:                0
% 4.18/1.02  inst_num_tautologies:                   0
% 4.18/1.02  inst_num_prop_implied:                  0
% 4.18/1.02  inst_num_existing_simplified:           0
% 4.18/1.02  inst_num_eq_res_simplified:             0
% 4.18/1.02  inst_num_child_elim:                    0
% 4.18/1.02  inst_num_of_dismatching_blockings:      1077
% 4.18/1.02  inst_num_of_non_proper_insts:           2320
% 4.18/1.02  inst_num_of_duplicates:                 0
% 4.18/1.02  inst_inst_num_from_inst_to_res:         0
% 4.18/1.02  inst_dismatching_checking_time:         0.
% 4.18/1.02  
% 4.18/1.02  ------ Resolution
% 4.18/1.02  
% 4.18/1.02  res_num_of_clauses:                     0
% 4.18/1.02  res_num_in_passive:                     0
% 4.18/1.02  res_num_in_active:                      0
% 4.18/1.02  res_num_of_loops:                       89
% 4.18/1.02  res_forward_subset_subsumed:            355
% 4.18/1.02  res_backward_subset_subsumed:           6
% 4.18/1.02  res_forward_subsumed:                   1
% 4.18/1.02  res_backward_subsumed:                  0
% 4.18/1.02  res_forward_subsumption_resolution:     1
% 4.18/1.02  res_backward_subsumption_resolution:    0
% 4.18/1.02  res_clause_to_clause_subsumption:       2560
% 4.18/1.02  res_orphan_elimination:                 0
% 4.18/1.02  res_tautology_del:                      179
% 4.18/1.02  res_num_eq_res_simplified:              0
% 4.18/1.02  res_num_sel_changes:                    0
% 4.18/1.02  res_moves_from_active_to_pass:          0
% 4.18/1.02  
% 4.18/1.02  ------ Superposition
% 4.18/1.02  
% 4.18/1.02  sup_time_total:                         0.
% 4.18/1.02  sup_time_generating:                    0.
% 4.18/1.02  sup_time_sim_full:                      0.
% 4.18/1.02  sup_time_sim_immed:                     0.
% 4.18/1.02  
% 4.18/1.02  sup_num_of_clauses:                     514
% 4.18/1.02  sup_num_in_active:                      139
% 4.18/1.02  sup_num_in_passive:                     375
% 4.18/1.02  sup_num_of_loops:                       166
% 4.18/1.02  sup_fw_superposition:                   427
% 4.18/1.02  sup_bw_superposition:                   457
% 4.18/1.02  sup_immediate_simplified:               260
% 4.18/1.02  sup_given_eliminated:                   2
% 4.18/1.02  comparisons_done:                       0
% 4.18/1.02  comparisons_avoided:                    2
% 4.18/1.02  
% 4.18/1.02  ------ Simplifications
% 4.18/1.02  
% 4.18/1.02  
% 4.18/1.02  sim_fw_subset_subsumed:                 130
% 4.18/1.02  sim_bw_subset_subsumed:                 12
% 4.18/1.02  sim_fw_subsumed:                        104
% 4.18/1.02  sim_bw_subsumed:                        11
% 4.18/1.02  sim_fw_subsumption_res:                 0
% 4.18/1.02  sim_bw_subsumption_res:                 0
% 4.18/1.02  sim_tautology_del:                      27
% 4.18/1.02  sim_eq_tautology_del:                   34
% 4.18/1.02  sim_eq_res_simp:                        2
% 4.18/1.02  sim_fw_demodulated:                     16
% 4.18/1.02  sim_bw_demodulated:                     11
% 4.18/1.02  sim_light_normalised:                   14
% 4.18/1.02  sim_joinable_taut:                      0
% 4.18/1.02  sim_joinable_simp:                      0
% 4.18/1.02  sim_ac_normalised:                      0
% 4.18/1.02  sim_smt_subsumption:                    0
% 4.18/1.02  
%------------------------------------------------------------------------------
