%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:33 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 258 expanded)
%              Number of clauses        :   77 ( 106 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  324 ( 871 expanded)
%              Number of equality atoms :  125 ( 188 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f30,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f29,f28])).

fof(f51,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f38,f38])).

fof(f52,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_841,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2850,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK3)
    | X0 != sK2
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_10631,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X1)
    | ~ r1_tarski(sK2,sK3)
    | X1 != sK3
    | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_21300,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3)
    | ~ r1_tarski(sK2,sK3)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_10631])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8861,plain,
    ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3))
    | ~ r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8863,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3)
    | r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_8861])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1190,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_448,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_449,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1239,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_449])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_457,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_458,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1240,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_458])).

cnf(c_1280,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1190,c_1239,c_1240])).

cnf(c_1196,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3429,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1196])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1197,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3539,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1197])).

cnf(c_3734,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3429,c_3539])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_430,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_431,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_433,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_26])).

cnf(c_1188,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1192,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1907,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1192])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1199,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2230,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_1907,c_1199])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2415,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2230,c_2])).

cnf(c_3737,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3734,c_2415])).

cnf(c_3738,plain,
    ( r1_tarski(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3737])).

cnf(c_3497,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2236,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2237,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_1755,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)))
    | k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_2175,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3))
    | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)))
    | k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK1,sK2),sK3)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_2177,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3))
    | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)))
    | k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK1,sK2),sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_838,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1290,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1390,plain,
    ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,X1))
    | X0 = sK2
    | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,X1)) ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_1706,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,X0))
    | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = sK2
    | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_1707,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2
    | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_1485,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1318,plain,
    ( ~ r1_tarski(sK2,X0)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1320,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_837,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1292,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1238,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1252,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_1285,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) != sK2
    | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,X0))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_1286,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != sK2
    | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1191,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1277,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1191,c_1239,c_1240])).

cnf(c_1278,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1277])).

cnf(c_1255,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_852,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_842,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_848,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_152,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_153,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_571,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_433])).

cnf(c_572,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_574,plain,
    ( r1_tarski(sK2,sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21300,c_8863,c_3738,c_3497,c_2237,c_2177,c_1707,c_1485,c_1320,c_1292,c_1286,c_1278,c_1255,c_852,c_848,c_574])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.58/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.58/1.53  
% 7.58/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.53  
% 7.58/1.53  ------  iProver source info
% 7.58/1.53  
% 7.58/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.53  git: non_committed_changes: false
% 7.58/1.53  git: last_make_outside_of_git: false
% 7.58/1.53  
% 7.58/1.53  ------ 
% 7.58/1.53  
% 7.58/1.53  ------ Input Options
% 7.58/1.53  
% 7.58/1.53  --out_options                           all
% 7.58/1.53  --tptp_safe_out                         true
% 7.58/1.53  --problem_path                          ""
% 7.58/1.53  --include_path                          ""
% 7.58/1.53  --clausifier                            res/vclausify_rel
% 7.58/1.53  --clausifier_options                    ""
% 7.58/1.53  --stdin                                 false
% 7.58/1.53  --stats_out                             all
% 7.58/1.53  
% 7.58/1.53  ------ General Options
% 7.58/1.53  
% 7.58/1.53  --fof                                   false
% 7.58/1.53  --time_out_real                         305.
% 7.58/1.53  --time_out_virtual                      -1.
% 7.58/1.53  --symbol_type_check                     false
% 7.58/1.53  --clausify_out                          false
% 7.58/1.53  --sig_cnt_out                           false
% 7.58/1.53  --trig_cnt_out                          false
% 7.58/1.53  --trig_cnt_out_tolerance                1.
% 7.58/1.53  --trig_cnt_out_sk_spl                   false
% 7.58/1.53  --abstr_cl_out                          false
% 7.58/1.53  
% 7.58/1.53  ------ Global Options
% 7.58/1.53  
% 7.58/1.53  --schedule                              default
% 7.58/1.53  --add_important_lit                     false
% 7.58/1.53  --prop_solver_per_cl                    1000
% 7.58/1.53  --min_unsat_core                        false
% 7.58/1.53  --soft_assumptions                      false
% 7.58/1.53  --soft_lemma_size                       3
% 7.58/1.53  --prop_impl_unit_size                   0
% 7.58/1.53  --prop_impl_unit                        []
% 7.58/1.53  --share_sel_clauses                     true
% 7.58/1.53  --reset_solvers                         false
% 7.58/1.53  --bc_imp_inh                            [conj_cone]
% 7.58/1.53  --conj_cone_tolerance                   3.
% 7.58/1.53  --extra_neg_conj                        none
% 7.58/1.53  --large_theory_mode                     true
% 7.58/1.53  --prolific_symb_bound                   200
% 7.58/1.53  --lt_threshold                          2000
% 7.58/1.53  --clause_weak_htbl                      true
% 7.58/1.53  --gc_record_bc_elim                     false
% 7.58/1.53  
% 7.58/1.53  ------ Preprocessing Options
% 7.58/1.53  
% 7.58/1.53  --preprocessing_flag                    true
% 7.58/1.53  --time_out_prep_mult                    0.1
% 7.58/1.53  --splitting_mode                        input
% 7.58/1.53  --splitting_grd                         true
% 7.58/1.53  --splitting_cvd                         false
% 7.58/1.53  --splitting_cvd_svl                     false
% 7.58/1.53  --splitting_nvd                         32
% 7.58/1.53  --sub_typing                            true
% 7.58/1.53  --prep_gs_sim                           true
% 7.58/1.53  --prep_unflatten                        true
% 7.58/1.53  --prep_res_sim                          true
% 7.58/1.53  --prep_upred                            true
% 7.58/1.53  --prep_sem_filter                       exhaustive
% 7.58/1.53  --prep_sem_filter_out                   false
% 7.58/1.53  --pred_elim                             true
% 7.58/1.53  --res_sim_input                         true
% 7.58/1.53  --eq_ax_congr_red                       true
% 7.58/1.53  --pure_diseq_elim                       true
% 7.58/1.53  --brand_transform                       false
% 7.58/1.53  --non_eq_to_eq                          false
% 7.58/1.53  --prep_def_merge                        true
% 7.58/1.53  --prep_def_merge_prop_impl              false
% 7.58/1.53  --prep_def_merge_mbd                    true
% 7.58/1.53  --prep_def_merge_tr_red                 false
% 7.58/1.53  --prep_def_merge_tr_cl                  false
% 7.58/1.53  --smt_preprocessing                     true
% 7.58/1.53  --smt_ac_axioms                         fast
% 7.58/1.53  --preprocessed_out                      false
% 7.58/1.53  --preprocessed_stats                    false
% 7.58/1.53  
% 7.58/1.53  ------ Abstraction refinement Options
% 7.58/1.53  
% 7.58/1.53  --abstr_ref                             []
% 7.58/1.53  --abstr_ref_prep                        false
% 7.58/1.53  --abstr_ref_until_sat                   false
% 7.58/1.53  --abstr_ref_sig_restrict                funpre
% 7.58/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.53  --abstr_ref_under                       []
% 7.58/1.53  
% 7.58/1.53  ------ SAT Options
% 7.58/1.53  
% 7.58/1.53  --sat_mode                              false
% 7.58/1.53  --sat_fm_restart_options                ""
% 7.58/1.53  --sat_gr_def                            false
% 7.58/1.53  --sat_epr_types                         true
% 7.58/1.53  --sat_non_cyclic_types                  false
% 7.58/1.53  --sat_finite_models                     false
% 7.58/1.53  --sat_fm_lemmas                         false
% 7.58/1.53  --sat_fm_prep                           false
% 7.58/1.53  --sat_fm_uc_incr                        true
% 7.58/1.53  --sat_out_model                         small
% 7.58/1.53  --sat_out_clauses                       false
% 7.58/1.53  
% 7.58/1.53  ------ QBF Options
% 7.58/1.53  
% 7.58/1.53  --qbf_mode                              false
% 7.58/1.53  --qbf_elim_univ                         false
% 7.58/1.53  --qbf_dom_inst                          none
% 7.58/1.53  --qbf_dom_pre_inst                      false
% 7.58/1.53  --qbf_sk_in                             false
% 7.58/1.53  --qbf_pred_elim                         true
% 7.58/1.53  --qbf_split                             512
% 7.58/1.53  
% 7.58/1.53  ------ BMC1 Options
% 7.58/1.53  
% 7.58/1.53  --bmc1_incremental                      false
% 7.58/1.53  --bmc1_axioms                           reachable_all
% 7.58/1.53  --bmc1_min_bound                        0
% 7.58/1.53  --bmc1_max_bound                        -1
% 7.58/1.53  --bmc1_max_bound_default                -1
% 7.58/1.53  --bmc1_symbol_reachability              true
% 7.58/1.53  --bmc1_property_lemmas                  false
% 7.58/1.53  --bmc1_k_induction                      false
% 7.58/1.53  --bmc1_non_equiv_states                 false
% 7.58/1.53  --bmc1_deadlock                         false
% 7.58/1.53  --bmc1_ucm                              false
% 7.58/1.53  --bmc1_add_unsat_core                   none
% 7.58/1.53  --bmc1_unsat_core_children              false
% 7.58/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.53  --bmc1_out_stat                         full
% 7.58/1.53  --bmc1_ground_init                      false
% 7.58/1.53  --bmc1_pre_inst_next_state              false
% 7.58/1.53  --bmc1_pre_inst_state                   false
% 7.58/1.53  --bmc1_pre_inst_reach_state             false
% 7.58/1.53  --bmc1_out_unsat_core                   false
% 7.58/1.53  --bmc1_aig_witness_out                  false
% 7.58/1.53  --bmc1_verbose                          false
% 7.58/1.53  --bmc1_dump_clauses_tptp                false
% 7.58/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.53  --bmc1_dump_file                        -
% 7.58/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.53  --bmc1_ucm_extend_mode                  1
% 7.58/1.53  --bmc1_ucm_init_mode                    2
% 7.58/1.53  --bmc1_ucm_cone_mode                    none
% 7.58/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.53  --bmc1_ucm_relax_model                  4
% 7.58/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.53  --bmc1_ucm_layered_model                none
% 7.58/1.53  --bmc1_ucm_max_lemma_size               10
% 7.58/1.53  
% 7.58/1.53  ------ AIG Options
% 7.58/1.53  
% 7.58/1.53  --aig_mode                              false
% 7.58/1.53  
% 7.58/1.53  ------ Instantiation Options
% 7.58/1.53  
% 7.58/1.53  --instantiation_flag                    true
% 7.58/1.53  --inst_sos_flag                         true
% 7.58/1.53  --inst_sos_phase                        true
% 7.58/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.53  --inst_lit_sel_side                     num_symb
% 7.58/1.53  --inst_solver_per_active                1400
% 7.58/1.53  --inst_solver_calls_frac                1.
% 7.58/1.53  --inst_passive_queue_type               priority_queues
% 7.58/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.53  --inst_passive_queues_freq              [25;2]
% 7.58/1.53  --inst_dismatching                      true
% 7.58/1.53  --inst_eager_unprocessed_to_passive     true
% 7.58/1.53  --inst_prop_sim_given                   true
% 7.58/1.53  --inst_prop_sim_new                     false
% 7.58/1.53  --inst_subs_new                         false
% 7.58/1.53  --inst_eq_res_simp                      false
% 7.58/1.53  --inst_subs_given                       false
% 7.58/1.53  --inst_orphan_elimination               true
% 7.58/1.53  --inst_learning_loop_flag               true
% 7.58/1.53  --inst_learning_start                   3000
% 7.58/1.53  --inst_learning_factor                  2
% 7.58/1.53  --inst_start_prop_sim_after_learn       3
% 7.58/1.53  --inst_sel_renew                        solver
% 7.58/1.53  --inst_lit_activity_flag                true
% 7.58/1.53  --inst_restr_to_given                   false
% 7.58/1.53  --inst_activity_threshold               500
% 7.58/1.53  --inst_out_proof                        true
% 7.58/1.53  
% 7.58/1.53  ------ Resolution Options
% 7.58/1.53  
% 7.58/1.53  --resolution_flag                       true
% 7.58/1.53  --res_lit_sel                           adaptive
% 7.58/1.53  --res_lit_sel_side                      none
% 7.58/1.53  --res_ordering                          kbo
% 7.58/1.53  --res_to_prop_solver                    active
% 7.58/1.53  --res_prop_simpl_new                    false
% 7.58/1.53  --res_prop_simpl_given                  true
% 7.58/1.53  --res_passive_queue_type                priority_queues
% 7.58/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.53  --res_passive_queues_freq               [15;5]
% 7.58/1.53  --res_forward_subs                      full
% 7.58/1.53  --res_backward_subs                     full
% 7.58/1.53  --res_forward_subs_resolution           true
% 7.58/1.53  --res_backward_subs_resolution          true
% 7.58/1.53  --res_orphan_elimination                true
% 7.58/1.53  --res_time_limit                        2.
% 7.58/1.53  --res_out_proof                         true
% 7.58/1.53  
% 7.58/1.53  ------ Superposition Options
% 7.58/1.53  
% 7.58/1.53  --superposition_flag                    true
% 7.58/1.53  --sup_passive_queue_type                priority_queues
% 7.58/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.53  --demod_completeness_check              fast
% 7.58/1.53  --demod_use_ground                      true
% 7.58/1.53  --sup_to_prop_solver                    passive
% 7.58/1.53  --sup_prop_simpl_new                    true
% 7.58/1.53  --sup_prop_simpl_given                  true
% 7.58/1.53  --sup_fun_splitting                     true
% 7.58/1.53  --sup_smt_interval                      50000
% 7.58/1.53  
% 7.58/1.53  ------ Superposition Simplification Setup
% 7.58/1.53  
% 7.58/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.53  --sup_immed_triv                        [TrivRules]
% 7.58/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.53  --sup_immed_bw_main                     []
% 7.58/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.53  --sup_input_bw                          []
% 7.58/1.53  
% 7.58/1.53  ------ Combination Options
% 7.58/1.53  
% 7.58/1.53  --comb_res_mult                         3
% 7.58/1.53  --comb_sup_mult                         2
% 7.58/1.53  --comb_inst_mult                        10
% 7.58/1.53  
% 7.58/1.53  ------ Debug Options
% 7.58/1.53  
% 7.58/1.53  --dbg_backtrace                         false
% 7.58/1.53  --dbg_dump_prop_clauses                 false
% 7.58/1.53  --dbg_dump_prop_clauses_file            -
% 7.58/1.53  --dbg_out_stat                          false
% 7.58/1.53  ------ Parsing...
% 7.58/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.53  
% 7.58/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.58/1.53  
% 7.58/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.53  
% 7.58/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.53  ------ Proving...
% 7.58/1.53  ------ Problem Properties 
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  clauses                                 18
% 7.58/1.53  conjectures                             2
% 7.58/1.53  EPR                                     0
% 7.58/1.53  Horn                                    16
% 7.58/1.53  unary                                   6
% 7.58/1.53  binary                                  10
% 7.58/1.53  lits                                    32
% 7.58/1.53  lits eq                                 11
% 7.58/1.53  fd_pure                                 0
% 7.58/1.53  fd_pseudo                               0
% 7.58/1.53  fd_cond                                 0
% 7.58/1.53  fd_pseudo_cond                          2
% 7.58/1.53  AC symbols                              0
% 7.58/1.53  
% 7.58/1.53  ------ Schedule dynamic 5 is on 
% 7.58/1.53  
% 7.58/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  ------ 
% 7.58/1.53  Current options:
% 7.58/1.53  ------ 
% 7.58/1.53  
% 7.58/1.53  ------ Input Options
% 7.58/1.53  
% 7.58/1.53  --out_options                           all
% 7.58/1.53  --tptp_safe_out                         true
% 7.58/1.53  --problem_path                          ""
% 7.58/1.53  --include_path                          ""
% 7.58/1.53  --clausifier                            res/vclausify_rel
% 7.58/1.53  --clausifier_options                    ""
% 7.58/1.53  --stdin                                 false
% 7.58/1.53  --stats_out                             all
% 7.58/1.53  
% 7.58/1.53  ------ General Options
% 7.58/1.53  
% 7.58/1.53  --fof                                   false
% 7.58/1.53  --time_out_real                         305.
% 7.58/1.53  --time_out_virtual                      -1.
% 7.58/1.53  --symbol_type_check                     false
% 7.58/1.53  --clausify_out                          false
% 7.58/1.53  --sig_cnt_out                           false
% 7.58/1.53  --trig_cnt_out                          false
% 7.58/1.53  --trig_cnt_out_tolerance                1.
% 7.58/1.53  --trig_cnt_out_sk_spl                   false
% 7.58/1.53  --abstr_cl_out                          false
% 7.58/1.53  
% 7.58/1.53  ------ Global Options
% 7.58/1.53  
% 7.58/1.53  --schedule                              default
% 7.58/1.53  --add_important_lit                     false
% 7.58/1.53  --prop_solver_per_cl                    1000
% 7.58/1.53  --min_unsat_core                        false
% 7.58/1.53  --soft_assumptions                      false
% 7.58/1.53  --soft_lemma_size                       3
% 7.58/1.53  --prop_impl_unit_size                   0
% 7.58/1.53  --prop_impl_unit                        []
% 7.58/1.53  --share_sel_clauses                     true
% 7.58/1.53  --reset_solvers                         false
% 7.58/1.53  --bc_imp_inh                            [conj_cone]
% 7.58/1.53  --conj_cone_tolerance                   3.
% 7.58/1.53  --extra_neg_conj                        none
% 7.58/1.53  --large_theory_mode                     true
% 7.58/1.53  --prolific_symb_bound                   200
% 7.58/1.53  --lt_threshold                          2000
% 7.58/1.53  --clause_weak_htbl                      true
% 7.58/1.53  --gc_record_bc_elim                     false
% 7.58/1.53  
% 7.58/1.53  ------ Preprocessing Options
% 7.58/1.53  
% 7.58/1.53  --preprocessing_flag                    true
% 7.58/1.53  --time_out_prep_mult                    0.1
% 7.58/1.53  --splitting_mode                        input
% 7.58/1.53  --splitting_grd                         true
% 7.58/1.53  --splitting_cvd                         false
% 7.58/1.53  --splitting_cvd_svl                     false
% 7.58/1.53  --splitting_nvd                         32
% 7.58/1.53  --sub_typing                            true
% 7.58/1.53  --prep_gs_sim                           true
% 7.58/1.53  --prep_unflatten                        true
% 7.58/1.53  --prep_res_sim                          true
% 7.58/1.53  --prep_upred                            true
% 7.58/1.53  --prep_sem_filter                       exhaustive
% 7.58/1.53  --prep_sem_filter_out                   false
% 7.58/1.53  --pred_elim                             true
% 7.58/1.53  --res_sim_input                         true
% 7.58/1.53  --eq_ax_congr_red                       true
% 7.58/1.53  --pure_diseq_elim                       true
% 7.58/1.53  --brand_transform                       false
% 7.58/1.53  --non_eq_to_eq                          false
% 7.58/1.53  --prep_def_merge                        true
% 7.58/1.53  --prep_def_merge_prop_impl              false
% 7.58/1.53  --prep_def_merge_mbd                    true
% 7.58/1.53  --prep_def_merge_tr_red                 false
% 7.58/1.53  --prep_def_merge_tr_cl                  false
% 7.58/1.53  --smt_preprocessing                     true
% 7.58/1.53  --smt_ac_axioms                         fast
% 7.58/1.53  --preprocessed_out                      false
% 7.58/1.53  --preprocessed_stats                    false
% 7.58/1.53  
% 7.58/1.53  ------ Abstraction refinement Options
% 7.58/1.53  
% 7.58/1.53  --abstr_ref                             []
% 7.58/1.53  --abstr_ref_prep                        false
% 7.58/1.53  --abstr_ref_until_sat                   false
% 7.58/1.53  --abstr_ref_sig_restrict                funpre
% 7.58/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.53  --abstr_ref_under                       []
% 7.58/1.53  
% 7.58/1.53  ------ SAT Options
% 7.58/1.53  
% 7.58/1.53  --sat_mode                              false
% 7.58/1.53  --sat_fm_restart_options                ""
% 7.58/1.53  --sat_gr_def                            false
% 7.58/1.53  --sat_epr_types                         true
% 7.58/1.53  --sat_non_cyclic_types                  false
% 7.58/1.53  --sat_finite_models                     false
% 7.58/1.53  --sat_fm_lemmas                         false
% 7.58/1.53  --sat_fm_prep                           false
% 7.58/1.53  --sat_fm_uc_incr                        true
% 7.58/1.53  --sat_out_model                         small
% 7.58/1.53  --sat_out_clauses                       false
% 7.58/1.53  
% 7.58/1.53  ------ QBF Options
% 7.58/1.53  
% 7.58/1.53  --qbf_mode                              false
% 7.58/1.53  --qbf_elim_univ                         false
% 7.58/1.53  --qbf_dom_inst                          none
% 7.58/1.53  --qbf_dom_pre_inst                      false
% 7.58/1.53  --qbf_sk_in                             false
% 7.58/1.53  --qbf_pred_elim                         true
% 7.58/1.53  --qbf_split                             512
% 7.58/1.53  
% 7.58/1.53  ------ BMC1 Options
% 7.58/1.53  
% 7.58/1.53  --bmc1_incremental                      false
% 7.58/1.53  --bmc1_axioms                           reachable_all
% 7.58/1.53  --bmc1_min_bound                        0
% 7.58/1.53  --bmc1_max_bound                        -1
% 7.58/1.53  --bmc1_max_bound_default                -1
% 7.58/1.53  --bmc1_symbol_reachability              true
% 7.58/1.53  --bmc1_property_lemmas                  false
% 7.58/1.53  --bmc1_k_induction                      false
% 7.58/1.53  --bmc1_non_equiv_states                 false
% 7.58/1.53  --bmc1_deadlock                         false
% 7.58/1.53  --bmc1_ucm                              false
% 7.58/1.53  --bmc1_add_unsat_core                   none
% 7.58/1.53  --bmc1_unsat_core_children              false
% 7.58/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.53  --bmc1_out_stat                         full
% 7.58/1.53  --bmc1_ground_init                      false
% 7.58/1.53  --bmc1_pre_inst_next_state              false
% 7.58/1.53  --bmc1_pre_inst_state                   false
% 7.58/1.53  --bmc1_pre_inst_reach_state             false
% 7.58/1.53  --bmc1_out_unsat_core                   false
% 7.58/1.53  --bmc1_aig_witness_out                  false
% 7.58/1.53  --bmc1_verbose                          false
% 7.58/1.53  --bmc1_dump_clauses_tptp                false
% 7.58/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.53  --bmc1_dump_file                        -
% 7.58/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.53  --bmc1_ucm_extend_mode                  1
% 7.58/1.53  --bmc1_ucm_init_mode                    2
% 7.58/1.53  --bmc1_ucm_cone_mode                    none
% 7.58/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.53  --bmc1_ucm_relax_model                  4
% 7.58/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.53  --bmc1_ucm_layered_model                none
% 7.58/1.53  --bmc1_ucm_max_lemma_size               10
% 7.58/1.53  
% 7.58/1.53  ------ AIG Options
% 7.58/1.53  
% 7.58/1.53  --aig_mode                              false
% 7.58/1.53  
% 7.58/1.53  ------ Instantiation Options
% 7.58/1.53  
% 7.58/1.53  --instantiation_flag                    true
% 7.58/1.53  --inst_sos_flag                         true
% 7.58/1.53  --inst_sos_phase                        true
% 7.58/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.53  --inst_lit_sel_side                     none
% 7.58/1.53  --inst_solver_per_active                1400
% 7.58/1.53  --inst_solver_calls_frac                1.
% 7.58/1.53  --inst_passive_queue_type               priority_queues
% 7.58/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.53  --inst_passive_queues_freq              [25;2]
% 7.58/1.53  --inst_dismatching                      true
% 7.58/1.53  --inst_eager_unprocessed_to_passive     true
% 7.58/1.53  --inst_prop_sim_given                   true
% 7.58/1.53  --inst_prop_sim_new                     false
% 7.58/1.53  --inst_subs_new                         false
% 7.58/1.53  --inst_eq_res_simp                      false
% 7.58/1.53  --inst_subs_given                       false
% 7.58/1.53  --inst_orphan_elimination               true
% 7.58/1.53  --inst_learning_loop_flag               true
% 7.58/1.53  --inst_learning_start                   3000
% 7.58/1.53  --inst_learning_factor                  2
% 7.58/1.53  --inst_start_prop_sim_after_learn       3
% 7.58/1.53  --inst_sel_renew                        solver
% 7.58/1.53  --inst_lit_activity_flag                true
% 7.58/1.53  --inst_restr_to_given                   false
% 7.58/1.53  --inst_activity_threshold               500
% 7.58/1.53  --inst_out_proof                        true
% 7.58/1.53  
% 7.58/1.53  ------ Resolution Options
% 7.58/1.53  
% 7.58/1.53  --resolution_flag                       false
% 7.58/1.53  --res_lit_sel                           adaptive
% 7.58/1.53  --res_lit_sel_side                      none
% 7.58/1.53  --res_ordering                          kbo
% 7.58/1.53  --res_to_prop_solver                    active
% 7.58/1.53  --res_prop_simpl_new                    false
% 7.58/1.53  --res_prop_simpl_given                  true
% 7.58/1.53  --res_passive_queue_type                priority_queues
% 7.58/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.53  --res_passive_queues_freq               [15;5]
% 7.58/1.53  --res_forward_subs                      full
% 7.58/1.53  --res_backward_subs                     full
% 7.58/1.53  --res_forward_subs_resolution           true
% 7.58/1.53  --res_backward_subs_resolution          true
% 7.58/1.53  --res_orphan_elimination                true
% 7.58/1.53  --res_time_limit                        2.
% 7.58/1.53  --res_out_proof                         true
% 7.58/1.53  
% 7.58/1.53  ------ Superposition Options
% 7.58/1.53  
% 7.58/1.53  --superposition_flag                    true
% 7.58/1.53  --sup_passive_queue_type                priority_queues
% 7.58/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.53  --demod_completeness_check              fast
% 7.58/1.53  --demod_use_ground                      true
% 7.58/1.53  --sup_to_prop_solver                    passive
% 7.58/1.53  --sup_prop_simpl_new                    true
% 7.58/1.53  --sup_prop_simpl_given                  true
% 7.58/1.53  --sup_fun_splitting                     true
% 7.58/1.53  --sup_smt_interval                      50000
% 7.58/1.53  
% 7.58/1.53  ------ Superposition Simplification Setup
% 7.58/1.53  
% 7.58/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.53  --sup_immed_triv                        [TrivRules]
% 7.58/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.53  --sup_immed_bw_main                     []
% 7.58/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.53  --sup_input_bw                          []
% 7.58/1.53  
% 7.58/1.53  ------ Combination Options
% 7.58/1.53  
% 7.58/1.53  --comb_res_mult                         3
% 7.58/1.53  --comb_sup_mult                         2
% 7.58/1.53  --comb_inst_mult                        10
% 7.58/1.53  
% 7.58/1.53  ------ Debug Options
% 7.58/1.53  
% 7.58/1.53  --dbg_backtrace                         false
% 7.58/1.53  --dbg_dump_prop_clauses                 false
% 7.58/1.53  --dbg_dump_prop_clauses_file            -
% 7.58/1.53  --dbg_out_stat                          false
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  ------ Proving...
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  % SZS status Theorem for theBenchmark.p
% 7.58/1.53  
% 7.58/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.53  
% 7.58/1.53  fof(f7,axiom,(
% 7.58/1.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f17,plain,(
% 7.58/1.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.58/1.53    inference(ennf_transformation,[],[f7])).
% 7.58/1.53  
% 7.58/1.53  fof(f37,plain,(
% 7.58/1.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.58/1.53    inference(cnf_transformation,[],[f17])).
% 7.58/1.53  
% 7.58/1.53  fof(f13,conjecture,(
% 7.58/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f14,negated_conjecture,(
% 7.58/1.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.58/1.53    inference(negated_conjecture,[],[f13])).
% 7.58/1.53  
% 7.58/1.53  fof(f20,plain,(
% 7.58/1.53    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.53    inference(ennf_transformation,[],[f14])).
% 7.58/1.53  
% 7.58/1.53  fof(f26,plain,(
% 7.58/1.53    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.53    inference(nnf_transformation,[],[f20])).
% 7.58/1.53  
% 7.58/1.53  fof(f27,plain,(
% 7.58/1.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.53    inference(flattening,[],[f26])).
% 7.58/1.53  
% 7.58/1.53  fof(f29,plain,(
% 7.58/1.53    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 7.58/1.53    introduced(choice_axiom,[])).
% 7.58/1.53  
% 7.58/1.53  fof(f28,plain,(
% 7.58/1.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.58/1.53    introduced(choice_axiom,[])).
% 7.58/1.53  
% 7.58/1.53  fof(f30,plain,(
% 7.58/1.53    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.58/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f29,f28])).
% 7.58/1.53  
% 7.58/1.53  fof(f51,plain,(
% 7.58/1.53    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 7.58/1.53    inference(cnf_transformation,[],[f30])).
% 7.58/1.53  
% 7.58/1.53  fof(f11,axiom,(
% 7.58/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f19,plain,(
% 7.58/1.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.53    inference(ennf_transformation,[],[f11])).
% 7.58/1.53  
% 7.58/1.53  fof(f47,plain,(
% 7.58/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.53    inference(cnf_transformation,[],[f19])).
% 7.58/1.53  
% 7.58/1.53  fof(f50,plain,(
% 7.58/1.53    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.58/1.53    inference(cnf_transformation,[],[f30])).
% 7.58/1.53  
% 7.58/1.53  fof(f49,plain,(
% 7.58/1.53    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.58/1.53    inference(cnf_transformation,[],[f30])).
% 7.58/1.53  
% 7.58/1.53  fof(f1,axiom,(
% 7.58/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f31,plain,(
% 7.58/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.58/1.53    inference(cnf_transformation,[],[f1])).
% 7.58/1.53  
% 7.58/1.53  fof(f6,axiom,(
% 7.58/1.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f16,plain,(
% 7.58/1.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.58/1.53    inference(ennf_transformation,[],[f6])).
% 7.58/1.53  
% 7.58/1.53  fof(f36,plain,(
% 7.58/1.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.58/1.53    inference(cnf_transformation,[],[f16])).
% 7.58/1.53  
% 7.58/1.53  fof(f10,axiom,(
% 7.58/1.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f18,plain,(
% 7.58/1.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.58/1.53    inference(ennf_transformation,[],[f10])).
% 7.58/1.53  
% 7.58/1.53  fof(f25,plain,(
% 7.58/1.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.58/1.53    inference(nnf_transformation,[],[f18])).
% 7.58/1.53  
% 7.58/1.53  fof(f43,plain,(
% 7.58/1.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.58/1.53    inference(cnf_transformation,[],[f25])).
% 7.58/1.53  
% 7.58/1.53  fof(f12,axiom,(
% 7.58/1.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f48,plain,(
% 7.58/1.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.58/1.53    inference(cnf_transformation,[],[f12])).
% 7.58/1.53  
% 7.58/1.53  fof(f9,axiom,(
% 7.58/1.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f21,plain,(
% 7.58/1.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.58/1.53    inference(nnf_transformation,[],[f9])).
% 7.58/1.53  
% 7.58/1.53  fof(f22,plain,(
% 7.58/1.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.58/1.53    inference(rectify,[],[f21])).
% 7.58/1.53  
% 7.58/1.53  fof(f23,plain,(
% 7.58/1.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.58/1.53    introduced(choice_axiom,[])).
% 7.58/1.53  
% 7.58/1.53  fof(f24,plain,(
% 7.58/1.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.58/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 7.58/1.53  
% 7.58/1.53  fof(f39,plain,(
% 7.58/1.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.58/1.53    inference(cnf_transformation,[],[f24])).
% 7.58/1.53  
% 7.58/1.53  fof(f57,plain,(
% 7.58/1.53    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.58/1.53    inference(equality_resolution,[],[f39])).
% 7.58/1.53  
% 7.58/1.53  fof(f4,axiom,(
% 7.58/1.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f15,plain,(
% 7.58/1.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.58/1.53    inference(ennf_transformation,[],[f4])).
% 7.58/1.53  
% 7.58/1.53  fof(f34,plain,(
% 7.58/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.58/1.53    inference(cnf_transformation,[],[f15])).
% 7.58/1.53  
% 7.58/1.53  fof(f8,axiom,(
% 7.58/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f38,plain,(
% 7.58/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.58/1.53    inference(cnf_transformation,[],[f8])).
% 7.58/1.53  
% 7.58/1.53  fof(f55,plain,(
% 7.58/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.58/1.53    inference(definition_unfolding,[],[f34,f38])).
% 7.58/1.53  
% 7.58/1.53  fof(f2,axiom,(
% 7.58/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.58/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.53  
% 7.58/1.53  fof(f32,plain,(
% 7.58/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.58/1.53    inference(cnf_transformation,[],[f2])).
% 7.58/1.53  
% 7.58/1.53  fof(f54,plain,(
% 7.58/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.58/1.53    inference(definition_unfolding,[],[f32,f38,f38])).
% 7.58/1.53  
% 7.58/1.53  fof(f52,plain,(
% 7.58/1.53    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 7.58/1.53    inference(cnf_transformation,[],[f30])).
% 7.58/1.53  
% 7.58/1.53  cnf(c_841,plain,
% 7.58/1.53      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.58/1.53      theory(equality) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2850,plain,
% 7.58/1.53      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK3) | X0 != sK2 | X1 != sK3 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_841]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_10631,plain,
% 7.58/1.53      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X1)
% 7.58/1.53      | ~ r1_tarski(sK2,sK3)
% 7.58/1.53      | X1 != sK3
% 7.58/1.53      | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) != sK2 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_2850]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_21300,plain,
% 7.58/1.53      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3)
% 7.58/1.53      | ~ r1_tarski(sK2,sK3)
% 7.58/1.53      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2
% 7.58/1.53      | sK3 != sK3 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_10631]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_6,plain,
% 7.58/1.53      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.58/1.53      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.58/1.53      inference(cnf_transformation,[],[f37]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_8861,plain,
% 7.58/1.53      ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3))
% 7.58/1.53      | ~ r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),sK3) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_6]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_8863,plain,
% 7.58/1.53      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3)
% 7.58/1.53      | r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3)) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_8861]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_18,negated_conjecture,
% 7.58/1.53      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.58/1.53      | r1_tarski(sK2,sK3) ),
% 7.58/1.53      inference(cnf_transformation,[],[f51]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1190,plain,
% 7.58/1.53      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.58/1.53      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.58/1.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_15,plain,
% 7.58/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.53      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.58/1.53      inference(cnf_transformation,[],[f47]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_19,negated_conjecture,
% 7.58/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.58/1.53      inference(cnf_transformation,[],[f50]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_448,plain,
% 7.58/1.53      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.58/1.53      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.58/1.53      | sK3 != X1 ),
% 7.58/1.53      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_449,plain,
% 7.58/1.53      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 7.58/1.53      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.58/1.53      inference(unflattening,[status(thm)],[c_448]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1239,plain,
% 7.58/1.53      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 7.58/1.53      inference(equality_resolution,[status(thm)],[c_449]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_20,negated_conjecture,
% 7.58/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.58/1.53      inference(cnf_transformation,[],[f49]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_457,plain,
% 7.58/1.53      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.58/1.53      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.58/1.53      | sK2 != X1 ),
% 7.58/1.53      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_458,plain,
% 7.58/1.53      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 7.58/1.53      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.58/1.53      inference(unflattening,[status(thm)],[c_457]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1240,plain,
% 7.58/1.53      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 7.58/1.53      inference(equality_resolution,[status(thm)],[c_458]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1280,plain,
% 7.58/1.53      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 7.58/1.53      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.58/1.53      inference(light_normalisation,[status(thm)],[c_1190,c_1239,c_1240]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1196,plain,
% 7.58/1.53      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 7.58/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 7.58/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_3429,plain,
% 7.58/1.53      ( r1_tarski(sK2,sK3) = iProver_top
% 7.58/1.53      | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 7.58/1.53      inference(superposition,[status(thm)],[c_1280,c_1196]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1,plain,
% 7.58/1.53      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.58/1.53      inference(cnf_transformation,[],[f31]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_5,plain,
% 7.58/1.53      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.58/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.58/1.53      inference(cnf_transformation,[],[f36]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1197,plain,
% 7.58/1.53      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.58/1.53      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 7.58/1.53      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_3539,plain,
% 7.58/1.53      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.58/1.53      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.58/1.53      inference(superposition,[status(thm)],[c_1,c_1197]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_3734,plain,
% 7.58/1.53      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top
% 7.58/1.53      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.58/1.53      inference(superposition,[status(thm)],[c_3429,c_3539]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_14,plain,
% 7.58/1.53      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.58/1.53      inference(cnf_transformation,[],[f43]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_430,plain,
% 7.58/1.53      ( r2_hidden(X0,X1)
% 7.58/1.53      | v1_xboole_0(X1)
% 7.58/1.53      | k1_zfmisc_1(sK1) != X1
% 7.58/1.53      | sK2 != X0 ),
% 7.58/1.53      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_431,plain,
% 7.58/1.53      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.58/1.53      inference(unflattening,[status(thm)],[c_430]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_16,plain,
% 7.58/1.53      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.58/1.53      inference(cnf_transformation,[],[f48]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_26,plain,
% 7.58/1.53      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_16]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_433,plain,
% 7.58/1.53      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 7.58/1.53      inference(global_propositional_subsumption,
% 7.58/1.53                [status(thm)],
% 7.58/1.53                [c_431,c_26]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1188,plain,
% 7.58/1.53      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.58/1.53      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_10,plain,
% 7.58/1.53      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.58/1.53      inference(cnf_transformation,[],[f57]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1192,plain,
% 7.58/1.53      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.58/1.53      | r1_tarski(X0,X1) = iProver_top ),
% 7.58/1.53      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1907,plain,
% 7.58/1.53      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.58/1.53      inference(superposition,[status(thm)],[c_1188,c_1192]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_3,plain,
% 7.58/1.53      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.58/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1199,plain,
% 7.58/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.58/1.53      | r1_tarski(X0,X1) != iProver_top ),
% 7.58/1.53      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2230,plain,
% 7.58/1.53      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 7.58/1.53      inference(superposition,[status(thm)],[c_1907,c_1199]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2,plain,
% 7.58/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.58/1.53      inference(cnf_transformation,[],[f54]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2415,plain,
% 7.58/1.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 7.58/1.53      inference(superposition,[status(thm)],[c_2230,c_2]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_3737,plain,
% 7.58/1.53      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.58/1.53      inference(light_normalisation,[status(thm)],[c_3734,c_2415]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_3738,plain,
% 7.58/1.53      ( r1_tarski(sK2,sK3) ),
% 7.58/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_3737]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_3497,plain,
% 7.58/1.53      ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2236,plain,
% 7.58/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_2]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2237,plain,
% 7.58/1.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_2236]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1755,plain,
% 7.58/1.53      ( ~ r1_tarski(X0,X1)
% 7.58/1.53      | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)))
% 7.58/1.53      | k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) != X1
% 7.58/1.53      | sK1 != X0 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_841]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2175,plain,
% 7.58/1.53      ( ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3))
% 7.58/1.53      | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)))
% 7.58/1.53      | k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK1,sK2),sK3)
% 7.58/1.53      | sK1 != X0 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1755]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_2177,plain,
% 7.58/1.53      ( ~ r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),sK3))
% 7.58/1.53      | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)))
% 7.58/1.53      | k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK1,sK2),sK3)
% 7.58/1.53      | sK1 != sK1 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_2175]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_838,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1290,plain,
% 7.58/1.53      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_838]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1390,plain,
% 7.58/1.53      ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,X1))
% 7.58/1.53      | X0 = sK2
% 7.58/1.53      | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,X1)) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1290]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1706,plain,
% 7.58/1.53      ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,X0))
% 7.58/1.53      | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = sK2
% 7.58/1.53      | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1390]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1707,plain,
% 7.58/1.53      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
% 7.58/1.53      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2
% 7.58/1.53      | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1706]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1485,plain,
% 7.58/1.53      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))
% 7.58/1.53      | ~ r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1318,plain,
% 7.58/1.53      ( ~ r1_tarski(sK2,X0)
% 7.58/1.53      | k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) = sK2 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_3]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1320,plain,
% 7.58/1.53      ( ~ r1_tarski(sK2,sK1)
% 7.58/1.53      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1318]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_837,plain,( X0 = X0 ),theory(equality) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1292,plain,
% 7.58/1.53      ( sK3 = sK3 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_837]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1238,plain,
% 7.58/1.53      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_838]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1252,plain,
% 7.58/1.53      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1238]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1285,plain,
% 7.58/1.53      ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) != sK2
% 7.58/1.53      | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,X0))
% 7.58/1.53      | sK2 != sK2 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1252]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1286,plain,
% 7.58/1.53      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != sK2
% 7.58/1.53      | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
% 7.58/1.53      | sK2 != sK2 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_1285]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_17,negated_conjecture,
% 7.58/1.53      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.58/1.53      | ~ r1_tarski(sK2,sK3) ),
% 7.58/1.53      inference(cnf_transformation,[],[f52]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1191,plain,
% 7.58/1.53      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 7.58/1.53      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.58/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1277,plain,
% 7.58/1.53      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 7.58/1.53      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.58/1.53      inference(light_normalisation,[status(thm)],[c_1191,c_1239,c_1240]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1278,plain,
% 7.58/1.53      ( ~ r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2))
% 7.58/1.53      | ~ r1_tarski(sK2,sK3) ),
% 7.58/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_1277]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_1255,plain,
% 7.58/1.53      ( sK2 = sK2 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_837]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_852,plain,
% 7.58/1.53      ( sK1 = sK1 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_837]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_842,plain,
% 7.58/1.53      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.58/1.53      theory(equality) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_848,plain,
% 7.58/1.53      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_842]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_152,plain,
% 7.58/1.53      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.58/1.53      inference(prop_impl,[status(thm)],[c_10]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_153,plain,
% 7.58/1.53      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.58/1.53      inference(renaming,[status(thm)],[c_152]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_571,plain,
% 7.58/1.53      ( r1_tarski(X0,X1)
% 7.58/1.53      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 7.58/1.53      | sK2 != X0 ),
% 7.58/1.53      inference(resolution_lifted,[status(thm)],[c_153,c_433]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_572,plain,
% 7.58/1.53      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.58/1.53      inference(unflattening,[status(thm)],[c_571]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(c_574,plain,
% 7.58/1.53      ( r1_tarski(sK2,sK1) | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 7.58/1.53      inference(instantiation,[status(thm)],[c_572]) ).
% 7.58/1.53  
% 7.58/1.53  cnf(contradiction,plain,
% 7.58/1.53      ( $false ),
% 7.58/1.53      inference(minisat,
% 7.58/1.53                [status(thm)],
% 7.58/1.53                [c_21300,c_8863,c_3738,c_3497,c_2237,c_2177,c_1707,
% 7.58/1.53                 c_1485,c_1320,c_1292,c_1286,c_1278,c_1255,c_852,c_848,
% 7.58/1.53                 c_574]) ).
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.53  
% 7.58/1.53  ------                               Statistics
% 7.58/1.53  
% 7.58/1.53  ------ General
% 7.58/1.53  
% 7.58/1.53  abstr_ref_over_cycles:                  0
% 7.58/1.53  abstr_ref_under_cycles:                 0
% 7.58/1.53  gc_basic_clause_elim:                   0
% 7.58/1.53  forced_gc_time:                         0
% 7.58/1.53  parsing_time:                           0.015
% 7.58/1.53  unif_index_cands_time:                  0.
% 7.58/1.53  unif_index_add_time:                    0.
% 7.58/1.53  orderings_time:                         0.
% 7.58/1.53  out_proof_time:                         0.01
% 7.58/1.53  total_time:                             0.665
% 7.58/1.53  num_of_symbols:                         44
% 7.58/1.53  num_of_terms:                           26013
% 7.58/1.53  
% 7.58/1.53  ------ Preprocessing
% 7.58/1.53  
% 7.58/1.53  num_of_splits:                          0
% 7.58/1.53  num_of_split_atoms:                     0
% 7.58/1.53  num_of_reused_defs:                     0
% 7.58/1.53  num_eq_ax_congr_red:                    18
% 7.58/1.53  num_of_sem_filtered_clauses:            1
% 7.58/1.53  num_of_subtypes:                        0
% 7.58/1.53  monotx_restored_types:                  0
% 7.58/1.53  sat_num_of_epr_types:                   0
% 7.58/1.53  sat_num_of_non_cyclic_types:            0
% 7.58/1.53  sat_guarded_non_collapsed_types:        0
% 7.58/1.53  num_pure_diseq_elim:                    0
% 7.58/1.53  simp_replaced_by:                       0
% 7.58/1.53  res_preprocessed:                       92
% 7.58/1.53  prep_upred:                             0
% 7.58/1.53  prep_unflattend:                        46
% 7.58/1.53  smt_new_axioms:                         0
% 7.58/1.53  pred_elim_cands:                        2
% 7.58/1.53  pred_elim:                              2
% 7.58/1.53  pred_elim_cl:                           3
% 7.58/1.53  pred_elim_cycles:                       5
% 7.58/1.53  merged_defs:                            24
% 7.58/1.53  merged_defs_ncl:                        0
% 7.58/1.53  bin_hyper_res:                          25
% 7.58/1.53  prep_cycles:                            4
% 7.58/1.53  pred_elim_time:                         0.006
% 7.58/1.53  splitting_time:                         0.
% 7.58/1.53  sem_filter_time:                        0.
% 7.58/1.53  monotx_time:                            0.
% 7.58/1.53  subtype_inf_time:                       0.
% 7.58/1.53  
% 7.58/1.53  ------ Problem properties
% 7.58/1.53  
% 7.58/1.53  clauses:                                18
% 7.58/1.53  conjectures:                            2
% 7.58/1.53  epr:                                    0
% 7.58/1.53  horn:                                   16
% 7.58/1.53  ground:                                 4
% 7.58/1.53  unary:                                  6
% 7.58/1.53  binary:                                 10
% 7.58/1.53  lits:                                   32
% 7.58/1.53  lits_eq:                                11
% 7.58/1.53  fd_pure:                                0
% 7.58/1.53  fd_pseudo:                              0
% 7.58/1.53  fd_cond:                                0
% 7.58/1.53  fd_pseudo_cond:                         2
% 7.58/1.53  ac_symbols:                             0
% 7.58/1.53  
% 7.58/1.53  ------ Propositional Solver
% 7.58/1.53  
% 7.58/1.53  prop_solver_calls:                      34
% 7.58/1.53  prop_fast_solver_calls:                 762
% 7.58/1.53  smt_solver_calls:                       0
% 7.58/1.53  smt_fast_solver_calls:                  0
% 7.58/1.53  prop_num_of_clauses:                    7933
% 7.58/1.53  prop_preprocess_simplified:             12225
% 7.58/1.53  prop_fo_subsumed:                       17
% 7.58/1.53  prop_solver_time:                       0.
% 7.58/1.53  smt_solver_time:                        0.
% 7.58/1.53  smt_fast_solver_time:                   0.
% 7.58/1.53  prop_fast_solver_time:                  0.
% 7.58/1.53  prop_unsat_core_time:                   0.001
% 7.58/1.53  
% 7.58/1.53  ------ QBF
% 7.58/1.53  
% 7.58/1.53  qbf_q_res:                              0
% 7.58/1.53  qbf_num_tautologies:                    0
% 7.58/1.53  qbf_prep_cycles:                        0
% 7.58/1.53  
% 7.58/1.53  ------ BMC1
% 7.58/1.53  
% 7.58/1.53  bmc1_current_bound:                     -1
% 7.58/1.53  bmc1_last_solved_bound:                 -1
% 7.58/1.53  bmc1_unsat_core_size:                   -1
% 7.58/1.53  bmc1_unsat_core_parents_size:           -1
% 7.58/1.53  bmc1_merge_next_fun:                    0
% 7.58/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.58/1.53  
% 7.58/1.53  ------ Instantiation
% 7.58/1.53  
% 7.58/1.53  inst_num_of_clauses:                    2085
% 7.58/1.53  inst_num_in_passive:                    284
% 7.58/1.53  inst_num_in_active:                     830
% 7.58/1.53  inst_num_in_unprocessed:                970
% 7.58/1.53  inst_num_of_loops:                      961
% 7.58/1.53  inst_num_of_learning_restarts:          0
% 7.58/1.53  inst_num_moves_active_passive:          123
% 7.58/1.53  inst_lit_activity:                      0
% 7.58/1.53  inst_lit_activity_moves:                0
% 7.58/1.53  inst_num_tautologies:                   0
% 7.58/1.53  inst_num_prop_implied:                  0
% 7.58/1.53  inst_num_existing_simplified:           0
% 7.58/1.53  inst_num_eq_res_simplified:             0
% 7.58/1.53  inst_num_child_elim:                    0
% 7.58/1.53  inst_num_of_dismatching_blockings:      1189
% 7.58/1.53  inst_num_of_non_proper_insts:           2165
% 7.58/1.53  inst_num_of_duplicates:                 0
% 7.58/1.53  inst_inst_num_from_inst_to_res:         0
% 7.58/1.53  inst_dismatching_checking_time:         0.
% 7.58/1.53  
% 7.58/1.53  ------ Resolution
% 7.58/1.53  
% 7.58/1.53  res_num_of_clauses:                     0
% 7.58/1.53  res_num_in_passive:                     0
% 7.58/1.53  res_num_in_active:                      0
% 7.58/1.53  res_num_of_loops:                       96
% 7.58/1.53  res_forward_subset_subsumed:            228
% 7.58/1.53  res_backward_subset_subsumed:           0
% 7.58/1.53  res_forward_subsumed:                   3
% 7.58/1.53  res_backward_subsumed:                  0
% 7.58/1.53  res_forward_subsumption_resolution:     2
% 7.58/1.53  res_backward_subsumption_resolution:    0
% 7.58/1.53  res_clause_to_clause_subsumption:       9322
% 7.58/1.53  res_orphan_elimination:                 0
% 7.58/1.53  res_tautology_del:                      276
% 7.58/1.53  res_num_eq_res_simplified:              0
% 7.58/1.53  res_num_sel_changes:                    0
% 7.58/1.53  res_moves_from_active_to_pass:          0
% 7.58/1.53  
% 7.58/1.53  ------ Superposition
% 7.58/1.53  
% 7.58/1.53  sup_time_total:                         0.
% 7.58/1.53  sup_time_generating:                    0.
% 7.58/1.53  sup_time_sim_full:                      0.
% 7.58/1.53  sup_time_sim_immed:                     0.
% 7.58/1.53  
% 7.58/1.53  sup_num_of_clauses:                     922
% 7.58/1.53  sup_num_in_active:                      155
% 7.58/1.53  sup_num_in_passive:                     767
% 7.58/1.53  sup_num_of_loops:                       192
% 7.58/1.53  sup_fw_superposition:                   1480
% 7.58/1.53  sup_bw_superposition:                   3320
% 7.58/1.53  sup_immediate_simplified:               2315
% 7.58/1.53  sup_given_eliminated:                   12
% 7.58/1.53  comparisons_done:                       0
% 7.58/1.53  comparisons_avoided:                    16
% 7.58/1.53  
% 7.58/1.53  ------ Simplifications
% 7.58/1.53  
% 7.58/1.53  
% 7.58/1.53  sim_fw_subset_subsumed:                 49
% 7.58/1.53  sim_bw_subset_subsumed:                 24
% 7.58/1.53  sim_fw_subsumed:                        374
% 7.58/1.53  sim_bw_subsumed:                        24
% 7.58/1.53  sim_fw_subsumption_res:                 0
% 7.58/1.53  sim_bw_subsumption_res:                 0
% 7.58/1.53  sim_tautology_del:                      24
% 7.58/1.53  sim_eq_tautology_del:                   383
% 7.58/1.53  sim_eq_res_simp:                        0
% 7.58/1.53  sim_fw_demodulated:                     1089
% 7.58/1.53  sim_bw_demodulated:                     171
% 7.58/1.53  sim_light_normalised:                   1472
% 7.58/1.53  sim_joinable_taut:                      0
% 7.58/1.53  sim_joinable_simp:                      0
% 7.58/1.53  sim_ac_normalised:                      0
% 7.58/1.53  sim_smt_subsumption:                    0
% 7.58/1.53  
%------------------------------------------------------------------------------
