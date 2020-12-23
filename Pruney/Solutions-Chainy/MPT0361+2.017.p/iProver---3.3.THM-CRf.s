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
% DateTime   : Thu Dec  3 11:40:27 EST 2020

% Result     : Theorem 27.99s
% Output     : CNFRefutation 27.99s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 312 expanded)
%              Number of clauses        :   96 ( 145 expanded)
%              Number of leaves         :   19 (  68 expanded)
%              Depth                    :   21
%              Number of atoms          :  346 ( 820 expanded)
%              Number of equality atoms :  137 ( 226 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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

fof(f35,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f34,f33])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
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
    inference(nnf_transformation,[],[f10])).

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

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_923,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_928,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1375,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_928])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1105,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_1564,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1375,c_24,c_31,c_1106])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_932,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2316,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1564,c_932])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_942,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2771,plain,
    ( k2_xboole_0(sK3,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2316,c_942])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_936,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1231,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_936])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_938,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3400,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_938])).

cnf(c_3404,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_938])).

cnf(c_3608,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_942])).

cnf(c_3615,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3608,c_2])).

cnf(c_18130,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3400,c_3615])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_922,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1376,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_928])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1588,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1376,c_23,c_31,c_1109])).

cnf(c_2317,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_932])).

cnf(c_4813,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2317,c_3615])).

cnf(c_7,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_937,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5141,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4813,c_937])).

cnf(c_1199,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1232,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_936])).

cnf(c_5979,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5141,c_1232])).

cnf(c_5998,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_5979,c_942])).

cnf(c_7671,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_5998])).

cnf(c_3373,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_937])).

cnf(c_14507,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(X0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7671,c_3373])).

cnf(c_48025,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK2),X0),k2_xboole_0(sK1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18130,c_14507])).

cnf(c_48087,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK2),X0),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_48025,c_2])).

cnf(c_50343,plain,
    ( r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48087,c_937])).

cnf(c_147211,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2771,c_50343])).

cnf(c_147528,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_147211])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_60644,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
    | ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_60645,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | r1_tarski(k2_xboole_0(sK2,sK3),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60644])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1412,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_29416,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
    | ~ r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_29417,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29416])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21676,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
    | k3_subset_1(X0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_21677,plain,
    ( k3_subset_1(X0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3))
    | m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21676])).

cnf(c_21679,plain,
    ( k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21677])).

cnf(c_4004,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10506,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4004])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1124,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
    | r1_tarski(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4254,plain,
    ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,X0)),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_10505,plain,
    ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4254])).

cnf(c_415,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1172,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(X2,X3),X4)
    | X1 != X4
    | X0 != k4_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1602,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | X0 != k4_xboole_0(X1,X2)
    | k3_subset_1(sK1,sK2) != X3 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_2393,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(sK1,sK2))
    | X0 != k4_xboole_0(X1,X2)
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_3044,plain,
    ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK2))
    | k3_subset_1(X0,X1) != k4_xboole_0(X0,X1)
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2393])).

cnf(c_8125,plain,
    ( r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | k3_subset_1(X0,k2_xboole_0(sK2,sK3)) != k4_xboole_0(X0,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3044])).

cnf(c_8128,plain,
    ( r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) != k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_8125])).

cnf(c_1535,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
    | k3_subset_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1673,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
    | k3_subset_1(sK1,sK2) != k3_subset_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_2944,plain,
    ( ~ r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(X1,X2))
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k3_subset_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_7569,plain,
    ( ~ r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2944])).

cnf(c_7571,plain,
    ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_7569])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2280,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_420,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_1711,plain,
    ( k4_subset_1(sK1,sK2,sK3) != X0
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X1,X0)
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_2279,plain,
    ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X0,k2_xboole_0(sK2,sK3))
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_2281,plain,
    ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
    | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_412,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1667,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_430,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_147528,c_60645,c_29417,c_21679,c_10506,c_10505,c_8128,c_7571,c_2280,c_2281,c_1667,c_1156,c_430,c_31,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.99/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.99/4.01  
% 27.99/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.99/4.01  
% 27.99/4.01  ------  iProver source info
% 27.99/4.01  
% 27.99/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.99/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.99/4.01  git: non_committed_changes: false
% 27.99/4.01  git: last_make_outside_of_git: false
% 27.99/4.01  
% 27.99/4.01  ------ 
% 27.99/4.01  
% 27.99/4.01  ------ Input Options
% 27.99/4.01  
% 27.99/4.01  --out_options                           all
% 27.99/4.01  --tptp_safe_out                         true
% 27.99/4.01  --problem_path                          ""
% 27.99/4.01  --include_path                          ""
% 27.99/4.01  --clausifier                            res/vclausify_rel
% 27.99/4.01  --clausifier_options                    --mode clausify
% 27.99/4.01  --stdin                                 false
% 27.99/4.01  --stats_out                             all
% 27.99/4.01  
% 27.99/4.01  ------ General Options
% 27.99/4.01  
% 27.99/4.01  --fof                                   false
% 27.99/4.01  --time_out_real                         305.
% 27.99/4.01  --time_out_virtual                      -1.
% 27.99/4.01  --symbol_type_check                     false
% 27.99/4.01  --clausify_out                          false
% 27.99/4.01  --sig_cnt_out                           false
% 27.99/4.01  --trig_cnt_out                          false
% 27.99/4.01  --trig_cnt_out_tolerance                1.
% 27.99/4.01  --trig_cnt_out_sk_spl                   false
% 27.99/4.01  --abstr_cl_out                          false
% 27.99/4.01  
% 27.99/4.01  ------ Global Options
% 27.99/4.01  
% 27.99/4.01  --schedule                              default
% 27.99/4.01  --add_important_lit                     false
% 27.99/4.01  --prop_solver_per_cl                    1000
% 27.99/4.01  --min_unsat_core                        false
% 27.99/4.01  --soft_assumptions                      false
% 27.99/4.01  --soft_lemma_size                       3
% 27.99/4.01  --prop_impl_unit_size                   0
% 27.99/4.01  --prop_impl_unit                        []
% 27.99/4.01  --share_sel_clauses                     true
% 27.99/4.01  --reset_solvers                         false
% 27.99/4.01  --bc_imp_inh                            [conj_cone]
% 27.99/4.01  --conj_cone_tolerance                   3.
% 27.99/4.01  --extra_neg_conj                        none
% 27.99/4.01  --large_theory_mode                     true
% 27.99/4.01  --prolific_symb_bound                   200
% 27.99/4.01  --lt_threshold                          2000
% 27.99/4.01  --clause_weak_htbl                      true
% 27.99/4.01  --gc_record_bc_elim                     false
% 27.99/4.01  
% 27.99/4.01  ------ Preprocessing Options
% 27.99/4.01  
% 27.99/4.01  --preprocessing_flag                    true
% 27.99/4.01  --time_out_prep_mult                    0.1
% 27.99/4.01  --splitting_mode                        input
% 27.99/4.01  --splitting_grd                         true
% 27.99/4.01  --splitting_cvd                         false
% 27.99/4.01  --splitting_cvd_svl                     false
% 27.99/4.01  --splitting_nvd                         32
% 27.99/4.01  --sub_typing                            true
% 27.99/4.01  --prep_gs_sim                           true
% 27.99/4.01  --prep_unflatten                        true
% 27.99/4.01  --prep_res_sim                          true
% 27.99/4.01  --prep_upred                            true
% 27.99/4.01  --prep_sem_filter                       exhaustive
% 27.99/4.01  --prep_sem_filter_out                   false
% 27.99/4.01  --pred_elim                             true
% 27.99/4.01  --res_sim_input                         true
% 27.99/4.01  --eq_ax_congr_red                       true
% 27.99/4.01  --pure_diseq_elim                       true
% 27.99/4.01  --brand_transform                       false
% 27.99/4.01  --non_eq_to_eq                          false
% 27.99/4.01  --prep_def_merge                        true
% 27.99/4.01  --prep_def_merge_prop_impl              false
% 27.99/4.01  --prep_def_merge_mbd                    true
% 27.99/4.01  --prep_def_merge_tr_red                 false
% 27.99/4.01  --prep_def_merge_tr_cl                  false
% 27.99/4.01  --smt_preprocessing                     true
% 27.99/4.01  --smt_ac_axioms                         fast
% 27.99/4.01  --preprocessed_out                      false
% 27.99/4.01  --preprocessed_stats                    false
% 27.99/4.01  
% 27.99/4.01  ------ Abstraction refinement Options
% 27.99/4.01  
% 27.99/4.01  --abstr_ref                             []
% 27.99/4.01  --abstr_ref_prep                        false
% 27.99/4.01  --abstr_ref_until_sat                   false
% 27.99/4.01  --abstr_ref_sig_restrict                funpre
% 27.99/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.99/4.01  --abstr_ref_under                       []
% 27.99/4.01  
% 27.99/4.01  ------ SAT Options
% 27.99/4.01  
% 27.99/4.01  --sat_mode                              false
% 27.99/4.01  --sat_fm_restart_options                ""
% 27.99/4.01  --sat_gr_def                            false
% 27.99/4.01  --sat_epr_types                         true
% 27.99/4.01  --sat_non_cyclic_types                  false
% 27.99/4.01  --sat_finite_models                     false
% 27.99/4.01  --sat_fm_lemmas                         false
% 27.99/4.01  --sat_fm_prep                           false
% 27.99/4.01  --sat_fm_uc_incr                        true
% 27.99/4.01  --sat_out_model                         small
% 27.99/4.01  --sat_out_clauses                       false
% 27.99/4.01  
% 27.99/4.01  ------ QBF Options
% 27.99/4.01  
% 27.99/4.01  --qbf_mode                              false
% 27.99/4.01  --qbf_elim_univ                         false
% 27.99/4.01  --qbf_dom_inst                          none
% 27.99/4.01  --qbf_dom_pre_inst                      false
% 27.99/4.01  --qbf_sk_in                             false
% 27.99/4.01  --qbf_pred_elim                         true
% 27.99/4.01  --qbf_split                             512
% 27.99/4.01  
% 27.99/4.01  ------ BMC1 Options
% 27.99/4.01  
% 27.99/4.01  --bmc1_incremental                      false
% 27.99/4.01  --bmc1_axioms                           reachable_all
% 27.99/4.01  --bmc1_min_bound                        0
% 27.99/4.01  --bmc1_max_bound                        -1
% 27.99/4.01  --bmc1_max_bound_default                -1
% 27.99/4.01  --bmc1_symbol_reachability              true
% 27.99/4.01  --bmc1_property_lemmas                  false
% 27.99/4.01  --bmc1_k_induction                      false
% 27.99/4.01  --bmc1_non_equiv_states                 false
% 27.99/4.01  --bmc1_deadlock                         false
% 27.99/4.01  --bmc1_ucm                              false
% 27.99/4.01  --bmc1_add_unsat_core                   none
% 27.99/4.01  --bmc1_unsat_core_children              false
% 27.99/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.99/4.01  --bmc1_out_stat                         full
% 27.99/4.01  --bmc1_ground_init                      false
% 27.99/4.01  --bmc1_pre_inst_next_state              false
% 27.99/4.01  --bmc1_pre_inst_state                   false
% 27.99/4.01  --bmc1_pre_inst_reach_state             false
% 27.99/4.01  --bmc1_out_unsat_core                   false
% 27.99/4.01  --bmc1_aig_witness_out                  false
% 27.99/4.01  --bmc1_verbose                          false
% 27.99/4.01  --bmc1_dump_clauses_tptp                false
% 27.99/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.99/4.01  --bmc1_dump_file                        -
% 27.99/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.99/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.99/4.01  --bmc1_ucm_extend_mode                  1
% 27.99/4.01  --bmc1_ucm_init_mode                    2
% 27.99/4.01  --bmc1_ucm_cone_mode                    none
% 27.99/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.99/4.01  --bmc1_ucm_relax_model                  4
% 27.99/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.99/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.99/4.01  --bmc1_ucm_layered_model                none
% 27.99/4.01  --bmc1_ucm_max_lemma_size               10
% 27.99/4.01  
% 27.99/4.01  ------ AIG Options
% 27.99/4.01  
% 27.99/4.01  --aig_mode                              false
% 27.99/4.01  
% 27.99/4.01  ------ Instantiation Options
% 27.99/4.01  
% 27.99/4.01  --instantiation_flag                    true
% 27.99/4.01  --inst_sos_flag                         false
% 27.99/4.01  --inst_sos_phase                        true
% 27.99/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.99/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.99/4.01  --inst_lit_sel_side                     num_symb
% 27.99/4.01  --inst_solver_per_active                1400
% 27.99/4.01  --inst_solver_calls_frac                1.
% 27.99/4.01  --inst_passive_queue_type               priority_queues
% 27.99/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.99/4.01  --inst_passive_queues_freq              [25;2]
% 27.99/4.01  --inst_dismatching                      true
% 27.99/4.01  --inst_eager_unprocessed_to_passive     true
% 27.99/4.01  --inst_prop_sim_given                   true
% 27.99/4.01  --inst_prop_sim_new                     false
% 27.99/4.01  --inst_subs_new                         false
% 27.99/4.01  --inst_eq_res_simp                      false
% 27.99/4.01  --inst_subs_given                       false
% 27.99/4.01  --inst_orphan_elimination               true
% 27.99/4.01  --inst_learning_loop_flag               true
% 27.99/4.01  --inst_learning_start                   3000
% 27.99/4.01  --inst_learning_factor                  2
% 27.99/4.01  --inst_start_prop_sim_after_learn       3
% 27.99/4.01  --inst_sel_renew                        solver
% 27.99/4.01  --inst_lit_activity_flag                true
% 27.99/4.01  --inst_restr_to_given                   false
% 27.99/4.01  --inst_activity_threshold               500
% 27.99/4.01  --inst_out_proof                        true
% 27.99/4.01  
% 27.99/4.01  ------ Resolution Options
% 27.99/4.01  
% 27.99/4.01  --resolution_flag                       true
% 27.99/4.01  --res_lit_sel                           adaptive
% 27.99/4.01  --res_lit_sel_side                      none
% 27.99/4.01  --res_ordering                          kbo
% 27.99/4.01  --res_to_prop_solver                    active
% 27.99/4.01  --res_prop_simpl_new                    false
% 27.99/4.01  --res_prop_simpl_given                  true
% 27.99/4.01  --res_passive_queue_type                priority_queues
% 27.99/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.99/4.01  --res_passive_queues_freq               [15;5]
% 27.99/4.01  --res_forward_subs                      full
% 27.99/4.01  --res_backward_subs                     full
% 27.99/4.01  --res_forward_subs_resolution           true
% 27.99/4.01  --res_backward_subs_resolution          true
% 27.99/4.01  --res_orphan_elimination                true
% 27.99/4.01  --res_time_limit                        2.
% 27.99/4.01  --res_out_proof                         true
% 27.99/4.01  
% 27.99/4.01  ------ Superposition Options
% 27.99/4.01  
% 27.99/4.01  --superposition_flag                    true
% 27.99/4.01  --sup_passive_queue_type                priority_queues
% 27.99/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.99/4.01  --sup_passive_queues_freq               [8;1;4]
% 27.99/4.01  --demod_completeness_check              fast
% 27.99/4.01  --demod_use_ground                      true
% 27.99/4.01  --sup_to_prop_solver                    passive
% 27.99/4.01  --sup_prop_simpl_new                    true
% 27.99/4.01  --sup_prop_simpl_given                  true
% 27.99/4.01  --sup_fun_splitting                     false
% 27.99/4.01  --sup_smt_interval                      50000
% 27.99/4.01  
% 27.99/4.01  ------ Superposition Simplification Setup
% 27.99/4.01  
% 27.99/4.01  --sup_indices_passive                   []
% 27.99/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.99/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.99/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.99/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.99/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.99/4.01  --sup_full_bw                           [BwDemod]
% 27.99/4.01  --sup_immed_triv                        [TrivRules]
% 27.99/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.99/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.99/4.01  --sup_immed_bw_main                     []
% 27.99/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.99/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.99/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.99/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.99/4.01  
% 27.99/4.01  ------ Combination Options
% 27.99/4.01  
% 27.99/4.01  --comb_res_mult                         3
% 27.99/4.01  --comb_sup_mult                         2
% 27.99/4.01  --comb_inst_mult                        10
% 27.99/4.01  
% 27.99/4.01  ------ Debug Options
% 27.99/4.01  
% 27.99/4.01  --dbg_backtrace                         false
% 27.99/4.01  --dbg_dump_prop_clauses                 false
% 27.99/4.01  --dbg_dump_prop_clauses_file            -
% 27.99/4.01  --dbg_out_stat                          false
% 27.99/4.01  ------ Parsing...
% 27.99/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.99/4.01  
% 27.99/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.99/4.01  
% 27.99/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.99/4.01  
% 27.99/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.99/4.01  ------ Proving...
% 27.99/4.01  ------ Problem Properties 
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  clauses                                 23
% 27.99/4.01  conjectures                             3
% 27.99/4.01  EPR                                     5
% 27.99/4.01  Horn                                    20
% 27.99/4.01  unary                                   8
% 27.99/4.01  binary                                  7
% 27.99/4.01  lits                                    46
% 27.99/4.01  lits eq                                 7
% 27.99/4.01  fd_pure                                 0
% 27.99/4.01  fd_pseudo                               0
% 27.99/4.01  fd_cond                                 0
% 27.99/4.01  fd_pseudo_cond                          2
% 27.99/4.01  AC symbols                              0
% 27.99/4.01  
% 27.99/4.01  ------ Schedule dynamic 5 is on 
% 27.99/4.01  
% 27.99/4.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  ------ 
% 27.99/4.01  Current options:
% 27.99/4.01  ------ 
% 27.99/4.01  
% 27.99/4.01  ------ Input Options
% 27.99/4.01  
% 27.99/4.01  --out_options                           all
% 27.99/4.01  --tptp_safe_out                         true
% 27.99/4.01  --problem_path                          ""
% 27.99/4.01  --include_path                          ""
% 27.99/4.01  --clausifier                            res/vclausify_rel
% 27.99/4.01  --clausifier_options                    --mode clausify
% 27.99/4.01  --stdin                                 false
% 27.99/4.01  --stats_out                             all
% 27.99/4.01  
% 27.99/4.01  ------ General Options
% 27.99/4.01  
% 27.99/4.01  --fof                                   false
% 27.99/4.01  --time_out_real                         305.
% 27.99/4.01  --time_out_virtual                      -1.
% 27.99/4.01  --symbol_type_check                     false
% 27.99/4.01  --clausify_out                          false
% 27.99/4.01  --sig_cnt_out                           false
% 27.99/4.01  --trig_cnt_out                          false
% 27.99/4.01  --trig_cnt_out_tolerance                1.
% 27.99/4.01  --trig_cnt_out_sk_spl                   false
% 27.99/4.01  --abstr_cl_out                          false
% 27.99/4.01  
% 27.99/4.01  ------ Global Options
% 27.99/4.01  
% 27.99/4.01  --schedule                              default
% 27.99/4.01  --add_important_lit                     false
% 27.99/4.01  --prop_solver_per_cl                    1000
% 27.99/4.01  --min_unsat_core                        false
% 27.99/4.01  --soft_assumptions                      false
% 27.99/4.01  --soft_lemma_size                       3
% 27.99/4.01  --prop_impl_unit_size                   0
% 27.99/4.01  --prop_impl_unit                        []
% 27.99/4.01  --share_sel_clauses                     true
% 27.99/4.01  --reset_solvers                         false
% 27.99/4.01  --bc_imp_inh                            [conj_cone]
% 27.99/4.01  --conj_cone_tolerance                   3.
% 27.99/4.01  --extra_neg_conj                        none
% 27.99/4.01  --large_theory_mode                     true
% 27.99/4.01  --prolific_symb_bound                   200
% 27.99/4.01  --lt_threshold                          2000
% 27.99/4.01  --clause_weak_htbl                      true
% 27.99/4.01  --gc_record_bc_elim                     false
% 27.99/4.01  
% 27.99/4.01  ------ Preprocessing Options
% 27.99/4.01  
% 27.99/4.01  --preprocessing_flag                    true
% 27.99/4.01  --time_out_prep_mult                    0.1
% 27.99/4.01  --splitting_mode                        input
% 27.99/4.01  --splitting_grd                         true
% 27.99/4.01  --splitting_cvd                         false
% 27.99/4.01  --splitting_cvd_svl                     false
% 27.99/4.01  --splitting_nvd                         32
% 27.99/4.01  --sub_typing                            true
% 27.99/4.01  --prep_gs_sim                           true
% 27.99/4.01  --prep_unflatten                        true
% 27.99/4.01  --prep_res_sim                          true
% 27.99/4.01  --prep_upred                            true
% 27.99/4.01  --prep_sem_filter                       exhaustive
% 27.99/4.01  --prep_sem_filter_out                   false
% 27.99/4.01  --pred_elim                             true
% 27.99/4.01  --res_sim_input                         true
% 27.99/4.01  --eq_ax_congr_red                       true
% 27.99/4.01  --pure_diseq_elim                       true
% 27.99/4.01  --brand_transform                       false
% 27.99/4.01  --non_eq_to_eq                          false
% 27.99/4.01  --prep_def_merge                        true
% 27.99/4.01  --prep_def_merge_prop_impl              false
% 27.99/4.01  --prep_def_merge_mbd                    true
% 27.99/4.01  --prep_def_merge_tr_red                 false
% 27.99/4.01  --prep_def_merge_tr_cl                  false
% 27.99/4.01  --smt_preprocessing                     true
% 27.99/4.01  --smt_ac_axioms                         fast
% 27.99/4.01  --preprocessed_out                      false
% 27.99/4.01  --preprocessed_stats                    false
% 27.99/4.01  
% 27.99/4.01  ------ Abstraction refinement Options
% 27.99/4.01  
% 27.99/4.01  --abstr_ref                             []
% 27.99/4.01  --abstr_ref_prep                        false
% 27.99/4.01  --abstr_ref_until_sat                   false
% 27.99/4.01  --abstr_ref_sig_restrict                funpre
% 27.99/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.99/4.01  --abstr_ref_under                       []
% 27.99/4.01  
% 27.99/4.01  ------ SAT Options
% 27.99/4.01  
% 27.99/4.01  --sat_mode                              false
% 27.99/4.01  --sat_fm_restart_options                ""
% 27.99/4.01  --sat_gr_def                            false
% 27.99/4.01  --sat_epr_types                         true
% 27.99/4.01  --sat_non_cyclic_types                  false
% 27.99/4.01  --sat_finite_models                     false
% 27.99/4.01  --sat_fm_lemmas                         false
% 27.99/4.01  --sat_fm_prep                           false
% 27.99/4.01  --sat_fm_uc_incr                        true
% 27.99/4.01  --sat_out_model                         small
% 27.99/4.01  --sat_out_clauses                       false
% 27.99/4.01  
% 27.99/4.01  ------ QBF Options
% 27.99/4.01  
% 27.99/4.01  --qbf_mode                              false
% 27.99/4.01  --qbf_elim_univ                         false
% 27.99/4.01  --qbf_dom_inst                          none
% 27.99/4.01  --qbf_dom_pre_inst                      false
% 27.99/4.01  --qbf_sk_in                             false
% 27.99/4.01  --qbf_pred_elim                         true
% 27.99/4.01  --qbf_split                             512
% 27.99/4.01  
% 27.99/4.01  ------ BMC1 Options
% 27.99/4.01  
% 27.99/4.01  --bmc1_incremental                      false
% 27.99/4.01  --bmc1_axioms                           reachable_all
% 27.99/4.01  --bmc1_min_bound                        0
% 27.99/4.01  --bmc1_max_bound                        -1
% 27.99/4.01  --bmc1_max_bound_default                -1
% 27.99/4.01  --bmc1_symbol_reachability              true
% 27.99/4.01  --bmc1_property_lemmas                  false
% 27.99/4.01  --bmc1_k_induction                      false
% 27.99/4.01  --bmc1_non_equiv_states                 false
% 27.99/4.01  --bmc1_deadlock                         false
% 27.99/4.01  --bmc1_ucm                              false
% 27.99/4.01  --bmc1_add_unsat_core                   none
% 27.99/4.01  --bmc1_unsat_core_children              false
% 27.99/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.99/4.01  --bmc1_out_stat                         full
% 27.99/4.01  --bmc1_ground_init                      false
% 27.99/4.01  --bmc1_pre_inst_next_state              false
% 27.99/4.01  --bmc1_pre_inst_state                   false
% 27.99/4.01  --bmc1_pre_inst_reach_state             false
% 27.99/4.01  --bmc1_out_unsat_core                   false
% 27.99/4.01  --bmc1_aig_witness_out                  false
% 27.99/4.01  --bmc1_verbose                          false
% 27.99/4.01  --bmc1_dump_clauses_tptp                false
% 27.99/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.99/4.01  --bmc1_dump_file                        -
% 27.99/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.99/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.99/4.01  --bmc1_ucm_extend_mode                  1
% 27.99/4.01  --bmc1_ucm_init_mode                    2
% 27.99/4.01  --bmc1_ucm_cone_mode                    none
% 27.99/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.99/4.01  --bmc1_ucm_relax_model                  4
% 27.99/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.99/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.99/4.01  --bmc1_ucm_layered_model                none
% 27.99/4.01  --bmc1_ucm_max_lemma_size               10
% 27.99/4.01  
% 27.99/4.01  ------ AIG Options
% 27.99/4.01  
% 27.99/4.01  --aig_mode                              false
% 27.99/4.01  
% 27.99/4.01  ------ Instantiation Options
% 27.99/4.01  
% 27.99/4.01  --instantiation_flag                    true
% 27.99/4.01  --inst_sos_flag                         false
% 27.99/4.01  --inst_sos_phase                        true
% 27.99/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.99/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.99/4.01  --inst_lit_sel_side                     none
% 27.99/4.01  --inst_solver_per_active                1400
% 27.99/4.01  --inst_solver_calls_frac                1.
% 27.99/4.01  --inst_passive_queue_type               priority_queues
% 27.99/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.99/4.01  --inst_passive_queues_freq              [25;2]
% 27.99/4.01  --inst_dismatching                      true
% 27.99/4.01  --inst_eager_unprocessed_to_passive     true
% 27.99/4.01  --inst_prop_sim_given                   true
% 27.99/4.01  --inst_prop_sim_new                     false
% 27.99/4.01  --inst_subs_new                         false
% 27.99/4.01  --inst_eq_res_simp                      false
% 27.99/4.01  --inst_subs_given                       false
% 27.99/4.01  --inst_orphan_elimination               true
% 27.99/4.01  --inst_learning_loop_flag               true
% 27.99/4.01  --inst_learning_start                   3000
% 27.99/4.01  --inst_learning_factor                  2
% 27.99/4.01  --inst_start_prop_sim_after_learn       3
% 27.99/4.01  --inst_sel_renew                        solver
% 27.99/4.01  --inst_lit_activity_flag                true
% 27.99/4.01  --inst_restr_to_given                   false
% 27.99/4.01  --inst_activity_threshold               500
% 27.99/4.01  --inst_out_proof                        true
% 27.99/4.01  
% 27.99/4.01  ------ Resolution Options
% 27.99/4.01  
% 27.99/4.01  --resolution_flag                       false
% 27.99/4.01  --res_lit_sel                           adaptive
% 27.99/4.01  --res_lit_sel_side                      none
% 27.99/4.01  --res_ordering                          kbo
% 27.99/4.01  --res_to_prop_solver                    active
% 27.99/4.01  --res_prop_simpl_new                    false
% 27.99/4.01  --res_prop_simpl_given                  true
% 27.99/4.01  --res_passive_queue_type                priority_queues
% 27.99/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.99/4.01  --res_passive_queues_freq               [15;5]
% 27.99/4.01  --res_forward_subs                      full
% 27.99/4.01  --res_backward_subs                     full
% 27.99/4.01  --res_forward_subs_resolution           true
% 27.99/4.01  --res_backward_subs_resolution          true
% 27.99/4.01  --res_orphan_elimination                true
% 27.99/4.01  --res_time_limit                        2.
% 27.99/4.01  --res_out_proof                         true
% 27.99/4.01  
% 27.99/4.01  ------ Superposition Options
% 27.99/4.01  
% 27.99/4.01  --superposition_flag                    true
% 27.99/4.01  --sup_passive_queue_type                priority_queues
% 27.99/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.99/4.01  --sup_passive_queues_freq               [8;1;4]
% 27.99/4.01  --demod_completeness_check              fast
% 27.99/4.01  --demod_use_ground                      true
% 27.99/4.01  --sup_to_prop_solver                    passive
% 27.99/4.01  --sup_prop_simpl_new                    true
% 27.99/4.01  --sup_prop_simpl_given                  true
% 27.99/4.01  --sup_fun_splitting                     false
% 27.99/4.01  --sup_smt_interval                      50000
% 27.99/4.01  
% 27.99/4.01  ------ Superposition Simplification Setup
% 27.99/4.01  
% 27.99/4.01  --sup_indices_passive                   []
% 27.99/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.99/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.99/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.99/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.99/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.99/4.01  --sup_full_bw                           [BwDemod]
% 27.99/4.01  --sup_immed_triv                        [TrivRules]
% 27.99/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.99/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.99/4.01  --sup_immed_bw_main                     []
% 27.99/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.99/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.99/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.99/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.99/4.01  
% 27.99/4.01  ------ Combination Options
% 27.99/4.01  
% 27.99/4.01  --comb_res_mult                         3
% 27.99/4.01  --comb_sup_mult                         2
% 27.99/4.01  --comb_inst_mult                        10
% 27.99/4.01  
% 27.99/4.01  ------ Debug Options
% 27.99/4.01  
% 27.99/4.01  --dbg_backtrace                         false
% 27.99/4.01  --dbg_dump_prop_clauses                 false
% 27.99/4.01  --dbg_dump_prop_clauses_file            -
% 27.99/4.01  --dbg_out_stat                          false
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  ------ Proving...
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  % SZS status Theorem for theBenchmark.p
% 27.99/4.01  
% 27.99/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.99/4.01  
% 27.99/4.01  fof(f1,axiom,(
% 27.99/4.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f36,plain,(
% 27.99/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.99/4.01    inference(cnf_transformation,[],[f1])).
% 27.99/4.01  
% 27.99/4.01  fof(f15,conjecture,(
% 27.99/4.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f16,negated_conjecture,(
% 27.99/4.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 27.99/4.01    inference(negated_conjecture,[],[f15])).
% 27.99/4.01  
% 27.99/4.01  fof(f27,plain,(
% 27.99/4.01    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.99/4.01    inference(ennf_transformation,[],[f16])).
% 27.99/4.01  
% 27.99/4.01  fof(f34,plain,(
% 27.99/4.01    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 27.99/4.01    introduced(choice_axiom,[])).
% 27.99/4.01  
% 27.99/4.01  fof(f33,plain,(
% 27.99/4.01    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 27.99/4.01    introduced(choice_axiom,[])).
% 27.99/4.01  
% 27.99/4.01  fof(f35,plain,(
% 27.99/4.01    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 27.99/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f34,f33])).
% 27.99/4.01  
% 27.99/4.01  fof(f57,plain,(
% 27.99/4.01    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 27.99/4.01    inference(cnf_transformation,[],[f35])).
% 27.99/4.01  
% 27.99/4.01  fof(f11,axiom,(
% 27.99/4.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f23,plain,(
% 27.99/4.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 27.99/4.01    inference(ennf_transformation,[],[f11])).
% 27.99/4.01  
% 27.99/4.01  fof(f32,plain,(
% 27.99/4.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 27.99/4.01    inference(nnf_transformation,[],[f23])).
% 27.99/4.01  
% 27.99/4.01  fof(f49,plain,(
% 27.99/4.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 27.99/4.01    inference(cnf_transformation,[],[f32])).
% 27.99/4.01  
% 27.99/4.01  fof(f13,axiom,(
% 27.99/4.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f54,plain,(
% 27.99/4.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 27.99/4.01    inference(cnf_transformation,[],[f13])).
% 27.99/4.01  
% 27.99/4.01  fof(f10,axiom,(
% 27.99/4.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f28,plain,(
% 27.99/4.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.99/4.01    inference(nnf_transformation,[],[f10])).
% 27.99/4.01  
% 27.99/4.01  fof(f29,plain,(
% 27.99/4.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.99/4.01    inference(rectify,[],[f28])).
% 27.99/4.01  
% 27.99/4.01  fof(f30,plain,(
% 27.99/4.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 27.99/4.01    introduced(choice_axiom,[])).
% 27.99/4.01  
% 27.99/4.01  fof(f31,plain,(
% 27.99/4.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 27.99/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 27.99/4.01  
% 27.99/4.01  fof(f45,plain,(
% 27.99/4.01    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 27.99/4.01    inference(cnf_transformation,[],[f31])).
% 27.99/4.01  
% 27.99/4.01  fof(f60,plain,(
% 27.99/4.01    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 27.99/4.01    inference(equality_resolution,[],[f45])).
% 27.99/4.01  
% 27.99/4.01  fof(f2,axiom,(
% 27.99/4.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f17,plain,(
% 27.99/4.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 27.99/4.01    inference(ennf_transformation,[],[f2])).
% 27.99/4.01  
% 27.99/4.01  fof(f37,plain,(
% 27.99/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 27.99/4.01    inference(cnf_transformation,[],[f17])).
% 27.99/4.01  
% 27.99/4.01  fof(f3,axiom,(
% 27.99/4.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f38,plain,(
% 27.99/4.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.99/4.01    inference(cnf_transformation,[],[f3])).
% 27.99/4.01  
% 27.99/4.01  fof(f9,axiom,(
% 27.99/4.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f44,plain,(
% 27.99/4.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.99/4.01    inference(cnf_transformation,[],[f9])).
% 27.99/4.01  
% 27.99/4.01  fof(f7,axiom,(
% 27.99/4.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f21,plain,(
% 27.99/4.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 27.99/4.01    inference(ennf_transformation,[],[f7])).
% 27.99/4.01  
% 27.99/4.01  fof(f42,plain,(
% 27.99/4.01    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 27.99/4.01    inference(cnf_transformation,[],[f21])).
% 27.99/4.01  
% 27.99/4.01  fof(f56,plain,(
% 27.99/4.01    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 27.99/4.01    inference(cnf_transformation,[],[f35])).
% 27.99/4.01  
% 27.99/4.01  fof(f8,axiom,(
% 27.99/4.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f22,plain,(
% 27.99/4.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 27.99/4.01    inference(ennf_transformation,[],[f8])).
% 27.99/4.01  
% 27.99/4.01  fof(f43,plain,(
% 27.99/4.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 27.99/4.01    inference(cnf_transformation,[],[f22])).
% 27.99/4.01  
% 27.99/4.01  fof(f46,plain,(
% 27.99/4.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 27.99/4.01    inference(cnf_transformation,[],[f31])).
% 27.99/4.01  
% 27.99/4.01  fof(f59,plain,(
% 27.99/4.01    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 27.99/4.01    inference(equality_resolution,[],[f46])).
% 27.99/4.01  
% 27.99/4.01  fof(f50,plain,(
% 27.99/4.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 27.99/4.01    inference(cnf_transformation,[],[f32])).
% 27.99/4.01  
% 27.99/4.01  fof(f12,axiom,(
% 27.99/4.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f24,plain,(
% 27.99/4.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.99/4.01    inference(ennf_transformation,[],[f12])).
% 27.99/4.01  
% 27.99/4.01  fof(f53,plain,(
% 27.99/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.99/4.01    inference(cnf_transformation,[],[f24])).
% 27.99/4.01  
% 27.99/4.01  fof(f5,axiom,(
% 27.99/4.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f20,plain,(
% 27.99/4.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 27.99/4.01    inference(ennf_transformation,[],[f5])).
% 27.99/4.01  
% 27.99/4.01  fof(f40,plain,(
% 27.99/4.01    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 27.99/4.01    inference(cnf_transformation,[],[f20])).
% 27.99/4.01  
% 27.99/4.01  fof(f14,axiom,(
% 27.99/4.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 27.99/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.99/4.01  
% 27.99/4.01  fof(f25,plain,(
% 27.99/4.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.99/4.01    inference(ennf_transformation,[],[f14])).
% 27.99/4.01  
% 27.99/4.01  fof(f26,plain,(
% 27.99/4.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.99/4.01    inference(flattening,[],[f25])).
% 27.99/4.01  
% 27.99/4.01  fof(f55,plain,(
% 27.99/4.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.99/4.01    inference(cnf_transformation,[],[f26])).
% 27.99/4.01  
% 27.99/4.01  fof(f58,plain,(
% 27.99/4.01    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 27.99/4.01    inference(cnf_transformation,[],[f35])).
% 27.99/4.01  
% 27.99/4.01  cnf(c_0,plain,
% 27.99/4.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.99/4.01      inference(cnf_transformation,[],[f36]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_21,negated_conjecture,
% 27.99/4.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 27.99/4.01      inference(cnf_transformation,[],[f57]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_923,plain,
% 27.99/4.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_16,plain,
% 27.99/4.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 27.99/4.01      inference(cnf_transformation,[],[f49]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_928,plain,
% 27.99/4.01      ( m1_subset_1(X0,X1) != iProver_top
% 27.99/4.01      | r2_hidden(X0,X1) = iProver_top
% 27.99/4.01      | v1_xboole_0(X1) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1375,plain,
% 27.99/4.01      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_923,c_928]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_24,plain,
% 27.99/4.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_18,plain,
% 27.99/4.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 27.99/4.01      inference(cnf_transformation,[],[f54]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_29,plain,
% 27.99/4.01      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_31,plain,
% 27.99/4.01      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_29]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1105,plain,
% 27.99/4.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 27.99/4.01      | r2_hidden(sK3,k1_zfmisc_1(sK1))
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_16]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1106,plain,
% 27.99/4.01      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 27.99/4.01      | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_1105]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1564,plain,
% 27.99/4.01      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(global_propositional_subsumption,
% 27.99/4.01                [status(thm)],
% 27.99/4.01                [c_1375,c_24,c_31,c_1106]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_12,plain,
% 27.99/4.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.99/4.01      inference(cnf_transformation,[],[f60]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_932,plain,
% 27.99/4.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.99/4.01      | r1_tarski(X0,X1) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2316,plain,
% 27.99/4.01      ( r1_tarski(sK3,sK1) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_1564,c_932]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1,plain,
% 27.99/4.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 27.99/4.01      inference(cnf_transformation,[],[f37]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_942,plain,
% 27.99/4.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2771,plain,
% 27.99/4.01      ( k2_xboole_0(sK3,sK1) = sK1 ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_2316,c_942]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2,plain,
% 27.99/4.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.99/4.01      inference(cnf_transformation,[],[f38]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_8,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.99/4.01      inference(cnf_transformation,[],[f44]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_936,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1231,plain,
% 27.99/4.01      ( r1_tarski(X0,X0) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_2,c_936]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_6,plain,
% 27.99/4.01      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 27.99/4.01      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 27.99/4.01      inference(cnf_transformation,[],[f42]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_938,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 27.99/4.01      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_3400,plain,
% 27.99/4.01      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_1231,c_938]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_3404,plain,
% 27.99/4.01      ( r1_tarski(X0,X1) != iProver_top
% 27.99/4.01      | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_2,c_938]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_3608,plain,
% 27.99/4.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k1_xboole_0
% 27.99/4.01      | r1_tarski(X0,X1) != iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_3404,c_942]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_3615,plain,
% 27.99/4.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 27.99/4.01      | r1_tarski(X0,X1) != iProver_top ),
% 27.99/4.01      inference(demodulation,[status(thm)],[c_3608,c_2]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_18130,plain,
% 27.99/4.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = k1_xboole_0 ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_3400,c_3615]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_22,negated_conjecture,
% 27.99/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 27.99/4.01      inference(cnf_transformation,[],[f56]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_922,plain,
% 27.99/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1376,plain,
% 27.99/4.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_922,c_928]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_23,plain,
% 27.99/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1108,plain,
% 27.99/4.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 27.99/4.01      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_16]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1109,plain,
% 27.99/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 27.99/4.01      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1588,plain,
% 27.99/4.01      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(global_propositional_subsumption,
% 27.99/4.01                [status(thm)],
% 27.99/4.01                [c_1376,c_23,c_31,c_1109]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2317,plain,
% 27.99/4.01      ( r1_tarski(sK2,sK1) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_1588,c_932]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_4813,plain,
% 27.99/4.01      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_2317,c_3615]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_7,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 27.99/4.01      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 27.99/4.01      inference(cnf_transformation,[],[f43]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_937,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 27.99/4.01      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_5141,plain,
% 27.99/4.01      ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top
% 27.99/4.01      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_4813,c_937]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1199,plain,
% 27.99/4.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1232,plain,
% 27.99/4.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_1199,c_936]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_5979,plain,
% 27.99/4.01      ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top ),
% 27.99/4.01      inference(global_propositional_subsumption,
% 27.99/4.01                [status(thm)],
% 27.99/4.01                [c_5141,c_1232]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_5998,plain,
% 27.99/4.01      ( k2_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_5979,c_942]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_7671,plain,
% 27.99/4.01      ( k2_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,X0) ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_0,c_5998]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_3373,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_936,c_937]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_14507,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(X0,sK2))) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_7671,c_3373]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_48025,plain,
% 27.99/4.01      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK2),X0),k2_xboole_0(sK1,k1_xboole_0)) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_18130,c_14507]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_48087,plain,
% 27.99/4.01      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK2),X0),sK1) = iProver_top ),
% 27.99/4.01      inference(demodulation,[status(thm)],[c_48025,c_2]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_50343,plain,
% 27.99/4.01      ( r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK1)) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_48087,c_937]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_147211,plain,
% 27.99/4.01      ( r1_tarski(k2_xboole_0(sK3,sK2),sK1) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_2771,c_50343]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_147528,plain,
% 27.99/4.01      ( r1_tarski(k2_xboole_0(sK2,sK3),sK1) = iProver_top ),
% 27.99/4.01      inference(superposition,[status(thm)],[c_0,c_147211]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_11,plain,
% 27.99/4.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.99/4.01      inference(cnf_transformation,[],[f59]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_60644,plain,
% 27.99/4.01      ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
% 27.99/4.01      | ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_11]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_60645,plain,
% 27.99/4.01      ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 27.99/4.01      | r1_tarski(k2_xboole_0(sK2,sK3),sK1) != iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_60644]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_15,plain,
% 27.99/4.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 27.99/4.01      inference(cnf_transformation,[],[f50]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1412,plain,
% 27.99/4.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.99/4.01      | ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_15]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_29416,plain,
% 27.99/4.01      ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
% 27.99/4.01      | ~ r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1))
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1412]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_29417,plain,
% 27.99/4.01      ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 27.99/4.01      | r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 27.99/4.01      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_29416]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_17,plain,
% 27.99/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.99/4.01      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 27.99/4.01      inference(cnf_transformation,[],[f53]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_21676,plain,
% 27.99/4.01      ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(X0))
% 27.99/4.01      | k3_subset_1(X0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_17]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_21677,plain,
% 27.99/4.01      ( k3_subset_1(X0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(X0)) != iProver_top ),
% 27.99/4.01      inference(predicate_to_equality,[status(thm)],[c_21676]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_21679,plain,
% 27.99/4.01      ( k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) != iProver_top ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_21677]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_4004,plain,
% 27.99/4.01      ( r1_tarski(X0,k2_xboole_0(X0,sK3)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_8]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_10506,plain,
% 27.99/4.01      ( r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_4004]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_4,plain,
% 27.99/4.01      ( ~ r1_tarski(X0,X1)
% 27.99/4.01      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 27.99/4.01      inference(cnf_transformation,[],[f40]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1124,plain,
% 27.99/4.01      ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
% 27.99/4.01      | r1_tarski(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X2,X0)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_4]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_4254,plain,
% 27.99/4.01      ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,X0)),k4_xboole_0(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1124]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_10505,plain,
% 27.99/4.01      ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_4254]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_415,plain,
% 27.99/4.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.99/4.01      theory(equality) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1172,plain,
% 27.99/4.01      ( r1_tarski(X0,X1)
% 27.99/4.01      | ~ r1_tarski(k4_xboole_0(X2,X3),X4)
% 27.99/4.01      | X1 != X4
% 27.99/4.01      | X0 != k4_xboole_0(X2,X3) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_415]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1602,plain,
% 27.99/4.01      ( r1_tarski(X0,k3_subset_1(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
% 27.99/4.01      | X0 != k4_xboole_0(X1,X2)
% 27.99/4.01      | k3_subset_1(sK1,sK2) != X3 ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1172]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2393,plain,
% 27.99/4.01      ( r1_tarski(X0,k3_subset_1(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(sK1,sK2))
% 27.99/4.01      | X0 != k4_xboole_0(X1,X2)
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1602]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_3044,plain,
% 27.99/4.01      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK2))
% 27.99/4.01      | k3_subset_1(X0,X1) != k4_xboole_0(X0,X1)
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_2393]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_8125,plain,
% 27.99/4.01      ( r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
% 27.99/4.01      | k3_subset_1(X0,k2_xboole_0(sK2,sK3)) != k4_xboole_0(X0,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_3044]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_8128,plain,
% 27.99/4.01      ( r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
% 27.99/4.01      | k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) != k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_8125]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1535,plain,
% 27.99/4.01      ( ~ r1_tarski(X0,X1)
% 27.99/4.01      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
% 27.99/4.01      | k3_subset_1(sK1,sK2) != X1 ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_415]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1673,plain,
% 27.99/4.01      ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 27.99/4.01      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != X0
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k3_subset_1(X1,X2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1535]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2944,plain,
% 27.99/4.01      ( ~ r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(X1,X2))
% 27.99/4.01      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k3_subset_1(X1,X2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1673]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_7569,plain,
% 27.99/4.01      ( ~ r1_tarski(k3_subset_1(X0,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(X0,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_2944]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_7571,plain,
% 27.99/4.01      ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | ~ r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k3_subset_1(sK1,sK2))
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) != k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_7569]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_19,plain,
% 27.99/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.99/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.99/4.01      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 27.99/4.01      inference(cnf_transformation,[],[f55]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1191,plain,
% 27.99/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
% 27.99/4.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 27.99/4.01      | k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_19]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2280,plain,
% 27.99/4.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 27.99/4.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 27.99/4.01      | k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1191]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_420,plain,
% 27.99/4.01      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 27.99/4.01      theory(equality) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1711,plain,
% 27.99/4.01      ( k4_subset_1(sK1,sK2,sK3) != X0
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X1,X0)
% 27.99/4.01      | sK1 != X1 ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_420]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2279,plain,
% 27.99/4.01      ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(X0,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | sK1 != X0 ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_1711]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_2281,plain,
% 27.99/4.01      ( k4_subset_1(sK1,sK2,sK3) != k2_xboole_0(sK2,sK3)
% 27.99/4.01      | k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)) = k3_subset_1(sK1,k2_xboole_0(sK2,sK3))
% 27.99/4.01      | sK1 != sK1 ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_2279]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_412,plain,( X0 = X0 ),theory(equality) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1667,plain,
% 27.99/4.01      ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_412]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_1156,plain,
% 27.99/4.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 27.99/4.01      | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_17]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_430,plain,
% 27.99/4.01      ( sK1 = sK1 ),
% 27.99/4.01      inference(instantiation,[status(thm)],[c_412]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(c_20,negated_conjecture,
% 27.99/4.01      ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
% 27.99/4.01      inference(cnf_transformation,[],[f58]) ).
% 27.99/4.01  
% 27.99/4.01  cnf(contradiction,plain,
% 27.99/4.01      ( $false ),
% 27.99/4.01      inference(minisat,
% 27.99/4.01                [status(thm)],
% 27.99/4.01                [c_147528,c_60645,c_29417,c_21679,c_10506,c_10505,c_8128,
% 27.99/4.01                 c_7571,c_2280,c_2281,c_1667,c_1156,c_430,c_31,c_20,c_21,
% 27.99/4.01                 c_22]) ).
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.99/4.01  
% 27.99/4.01  ------                               Statistics
% 27.99/4.01  
% 27.99/4.01  ------ General
% 27.99/4.01  
% 27.99/4.01  abstr_ref_over_cycles:                  0
% 27.99/4.01  abstr_ref_under_cycles:                 0
% 27.99/4.01  gc_basic_clause_elim:                   0
% 27.99/4.01  forced_gc_time:                         0
% 27.99/4.01  parsing_time:                           0.011
% 27.99/4.01  unif_index_cands_time:                  0.
% 27.99/4.01  unif_index_add_time:                    0.
% 27.99/4.01  orderings_time:                         0.
% 27.99/4.01  out_proof_time:                         0.016
% 27.99/4.01  total_time:                             3.454
% 27.99/4.01  num_of_symbols:                         45
% 27.99/4.01  num_of_terms:                           147121
% 27.99/4.01  
% 27.99/4.01  ------ Preprocessing
% 27.99/4.01  
% 27.99/4.01  num_of_splits:                          0
% 27.99/4.01  num_of_split_atoms:                     0
% 27.99/4.01  num_of_reused_defs:                     0
% 27.99/4.01  num_eq_ax_congr_red:                    10
% 27.99/4.01  num_of_sem_filtered_clauses:            1
% 27.99/4.01  num_of_subtypes:                        0
% 27.99/4.01  monotx_restored_types:                  0
% 27.99/4.01  sat_num_of_epr_types:                   0
% 27.99/4.01  sat_num_of_non_cyclic_types:            0
% 27.99/4.01  sat_guarded_non_collapsed_types:        0
% 27.99/4.01  num_pure_diseq_elim:                    0
% 27.99/4.01  simp_replaced_by:                       0
% 27.99/4.01  res_preprocessed:                       90
% 27.99/4.01  prep_upred:                             0
% 27.99/4.01  prep_unflattend:                        12
% 27.99/4.01  smt_new_axioms:                         0
% 27.99/4.01  pred_elim_cands:                        4
% 27.99/4.01  pred_elim:                              0
% 27.99/4.01  pred_elim_cl:                           0
% 27.99/4.01  pred_elim_cycles:                       1
% 27.99/4.01  merged_defs:                            12
% 27.99/4.01  merged_defs_ncl:                        0
% 27.99/4.01  bin_hyper_res:                          12
% 27.99/4.01  prep_cycles:                            3
% 27.99/4.01  pred_elim_time:                         0.002
% 27.99/4.01  splitting_time:                         0.
% 27.99/4.01  sem_filter_time:                        0.
% 27.99/4.01  monotx_time:                            0.001
% 27.99/4.01  subtype_inf_time:                       0.
% 27.99/4.01  
% 27.99/4.01  ------ Problem properties
% 27.99/4.01  
% 27.99/4.01  clauses:                                23
% 27.99/4.01  conjectures:                            3
% 27.99/4.01  epr:                                    5
% 27.99/4.01  horn:                                   20
% 27.99/4.01  ground:                                 3
% 27.99/4.01  unary:                                  8
% 27.99/4.01  binary:                                 7
% 27.99/4.01  lits:                                   46
% 27.99/4.01  lits_eq:                                7
% 27.99/4.01  fd_pure:                                0
% 27.99/4.01  fd_pseudo:                              0
% 27.99/4.01  fd_cond:                                0
% 27.99/4.01  fd_pseudo_cond:                         2
% 27.99/4.01  ac_symbols:                             0
% 27.99/4.01  
% 27.99/4.01  ------ Propositional Solver
% 27.99/4.01  
% 27.99/4.01  prop_solver_calls:                      46
% 27.99/4.01  prop_fast_solver_calls:                 1399
% 27.99/4.01  smt_solver_calls:                       0
% 27.99/4.01  smt_fast_solver_calls:                  0
% 27.99/4.01  prop_num_of_clauses:                    43574
% 27.99/4.01  prop_preprocess_simplified:             68792
% 27.99/4.01  prop_fo_subsumed:                       5
% 27.99/4.01  prop_solver_time:                       0.
% 27.99/4.01  smt_solver_time:                        0.
% 27.99/4.01  smt_fast_solver_time:                   0.
% 27.99/4.01  prop_fast_solver_time:                  0.
% 27.99/4.01  prop_unsat_core_time:                   0.004
% 27.99/4.01  
% 27.99/4.01  ------ QBF
% 27.99/4.01  
% 27.99/4.01  qbf_q_res:                              0
% 27.99/4.01  qbf_num_tautologies:                    0
% 27.99/4.01  qbf_prep_cycles:                        0
% 27.99/4.01  
% 27.99/4.01  ------ BMC1
% 27.99/4.01  
% 27.99/4.01  bmc1_current_bound:                     -1
% 27.99/4.01  bmc1_last_solved_bound:                 -1
% 27.99/4.01  bmc1_unsat_core_size:                   -1
% 27.99/4.01  bmc1_unsat_core_parents_size:           -1
% 27.99/4.01  bmc1_merge_next_fun:                    0
% 27.99/4.01  bmc1_unsat_core_clauses_time:           0.
% 27.99/4.01  
% 27.99/4.01  ------ Instantiation
% 27.99/4.01  
% 27.99/4.01  inst_num_of_clauses:                    1613
% 27.99/4.01  inst_num_in_passive:                    569
% 27.99/4.01  inst_num_in_active:                     2808
% 27.99/4.01  inst_num_in_unprocessed:                425
% 27.99/4.01  inst_num_of_loops:                      3639
% 27.99/4.01  inst_num_of_learning_restarts:          1
% 27.99/4.01  inst_num_moves_active_passive:          828
% 27.99/4.01  inst_lit_activity:                      0
% 27.99/4.01  inst_lit_activity_moves:                0
% 27.99/4.01  inst_num_tautologies:                   0
% 27.99/4.01  inst_num_prop_implied:                  0
% 27.99/4.01  inst_num_existing_simplified:           0
% 27.99/4.01  inst_num_eq_res_simplified:             0
% 27.99/4.01  inst_num_child_elim:                    0
% 27.99/4.01  inst_num_of_dismatching_blockings:      13475
% 27.99/4.01  inst_num_of_non_proper_insts:           11973
% 27.99/4.01  inst_num_of_duplicates:                 0
% 27.99/4.01  inst_inst_num_from_inst_to_res:         0
% 27.99/4.01  inst_dismatching_checking_time:         0.
% 27.99/4.01  
% 27.99/4.01  ------ Resolution
% 27.99/4.01  
% 27.99/4.01  res_num_of_clauses:                     33
% 27.99/4.01  res_num_in_passive:                     33
% 27.99/4.01  res_num_in_active:                      0
% 27.99/4.01  res_num_of_loops:                       93
% 27.99/4.01  res_forward_subset_subsumed:            634
% 27.99/4.01  res_backward_subset_subsumed:           16
% 27.99/4.01  res_forward_subsumed:                   0
% 27.99/4.01  res_backward_subsumed:                  0
% 27.99/4.01  res_forward_subsumption_resolution:     2
% 27.99/4.01  res_backward_subsumption_resolution:    0
% 27.99/4.01  res_clause_to_clause_subsumption:       62046
% 27.99/4.01  res_orphan_elimination:                 0
% 27.99/4.01  res_tautology_del:                      1046
% 27.99/4.01  res_num_eq_res_simplified:              0
% 27.99/4.01  res_num_sel_changes:                    0
% 27.99/4.01  res_moves_from_active_to_pass:          0
% 27.99/4.01  
% 27.99/4.01  ------ Superposition
% 27.99/4.01  
% 27.99/4.01  sup_time_total:                         0.
% 27.99/4.01  sup_time_generating:                    0.
% 27.99/4.01  sup_time_sim_full:                      0.
% 27.99/4.01  sup_time_sim_immed:                     0.
% 27.99/4.01  
% 27.99/4.01  sup_num_of_clauses:                     5718
% 27.99/4.01  sup_num_in_active:                      657
% 27.99/4.01  sup_num_in_passive:                     5061
% 27.99/4.01  sup_num_of_loops:                       726
% 27.99/4.01  sup_fw_superposition:                   12393
% 27.99/4.01  sup_bw_superposition:                   7518
% 27.99/4.01  sup_immediate_simplified:               10264
% 27.99/4.01  sup_given_eliminated:                   5
% 27.99/4.01  comparisons_done:                       0
% 27.99/4.01  comparisons_avoided:                    27
% 27.99/4.01  
% 27.99/4.01  ------ Simplifications
% 27.99/4.01  
% 27.99/4.01  
% 27.99/4.01  sim_fw_subset_subsumed:                 84
% 27.99/4.01  sim_bw_subset_subsumed:                 43
% 27.99/4.01  sim_fw_subsumed:                        1751
% 27.99/4.01  sim_bw_subsumed:                        40
% 27.99/4.01  sim_fw_subsumption_res:                 60
% 27.99/4.01  sim_bw_subsumption_res:                 0
% 27.99/4.01  sim_tautology_del:                      134
% 27.99/4.01  sim_eq_tautology_del:                   4390
% 27.99/4.01  sim_eq_res_simp:                        0
% 27.99/4.01  sim_fw_demodulated:                     6397
% 27.99/4.01  sim_bw_demodulated:                     400
% 27.99/4.01  sim_light_normalised:                   3270
% 27.99/4.01  sim_joinable_taut:                      0
% 27.99/4.01  sim_joinable_simp:                      0
% 27.99/4.01  sim_ac_normalised:                      0
% 27.99/4.01  sim_smt_subsumption:                    0
% 27.99/4.01  
%------------------------------------------------------------------------------
