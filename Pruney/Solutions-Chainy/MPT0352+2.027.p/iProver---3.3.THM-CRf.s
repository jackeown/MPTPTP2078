%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:35 EST 2020

% Result     : Theorem 11.14s
% Output     : CNFRefutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :  160 (1131 expanded)
%              Number of clauses        :  104 ( 465 expanded)
%              Number of leaves         :   17 ( 254 expanded)
%              Depth                    :   23
%              Number of atoms          :  361 (2490 expanded)
%              Number of equality atoms :  138 ( 930 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f33,f32])).

fof(f58,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f45,f45])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1259,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_475,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_476,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_1344,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_476])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_484,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_485,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_1345,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_485])).

cnf(c_1442,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1259,c_1344,c_1345])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1267,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1268,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2467,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1267,c_1268])).

cnf(c_3701,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_2467])).

cnf(c_3703,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3701,c_2467])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1265,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2112,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1265])).

cnf(c_3803,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_2112])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1271,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5465,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1271])).

cnf(c_6140,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3803,c_5465])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1266,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6399,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6140,c_1266])).

cnf(c_11233,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6399,c_5465])).

cnf(c_11405,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_11233])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1260,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1439,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1260,c_1344,c_1345])).

cnf(c_4553,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1439])).

cnf(c_11510,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11405,c_4553])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1269,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2666,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1269])).

cnf(c_4981,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_2666])).

cnf(c_11570,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0))),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11510,c_4981])).

cnf(c_11624,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11570,c_3703])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_177,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_178,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_366,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X0 != X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_16])).

cnf(c_367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_367,c_19])).

cnf(c_423,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_18,c_13,c_377])).

cnf(c_689,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_690,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_689])).

cnf(c_728,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_423,c_690])).

cnf(c_1256,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2114,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1265,c_1256])).

cnf(c_2394,plain,
    ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_2114])).

cnf(c_4546,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k3_subset_1(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_1266])).

cnf(c_2389,plain,
    ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2112,c_1256])).

cnf(c_4554,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4546,c_2389])).

cnf(c_1787,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_2468,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1265,c_1268])).

cnf(c_3449,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1787,c_1787,c_2468])).

cnf(c_3454,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_3449])).

cnf(c_3580,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_3454])).

cnf(c_4525,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_3580])).

cnf(c_32777,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_4525])).

cnf(c_11401,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1265,c_11233])).

cnf(c_32814,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_32777,c_11401])).

cnf(c_3809,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3703,c_0])).

cnf(c_2662,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1269])).

cnf(c_5129,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3809,c_2662])).

cnf(c_6141,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5129,c_5465])).

cnf(c_6142,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6140,c_6141])).

cnf(c_3798,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3703,c_3454])).

cnf(c_6361,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_6140,c_3798])).

cnf(c_32815,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_32814,c_9,c_6142,c_6361])).

cnf(c_33132,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_32815,c_3449])).

cnf(c_2387,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2112])).

cnf(c_11407,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2387,c_11233])).

cnf(c_33481,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_33132,c_11407])).

cnf(c_33482,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_33481,c_2467,c_3703])).

cnf(c_43912,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4554,c_33482])).

cnf(c_43939,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11624,c_43912])).

cnf(c_44917,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_43939,c_2666])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_457,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_458,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_460,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_29])).

cnf(c_1257,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_1261,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2462,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1261])).

cnf(c_11404,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2462,c_11233])).

cnf(c_12000,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11404,c_0])).

cnf(c_12042,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_12000,c_3703])).

cnf(c_44922,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_44917,c_12042])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44922,c_4553])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:18:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.14/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.14/1.99  
% 11.14/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.14/1.99  
% 11.14/1.99  ------  iProver source info
% 11.14/1.99  
% 11.14/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.14/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.14/1.99  git: non_committed_changes: false
% 11.14/1.99  git: last_make_outside_of_git: false
% 11.14/1.99  
% 11.14/1.99  ------ 
% 11.14/1.99  
% 11.14/1.99  ------ Input Options
% 11.14/1.99  
% 11.14/1.99  --out_options                           all
% 11.14/1.99  --tptp_safe_out                         true
% 11.14/1.99  --problem_path                          ""
% 11.14/1.99  --include_path                          ""
% 11.14/1.99  --clausifier                            res/vclausify_rel
% 11.14/1.99  --clausifier_options                    ""
% 11.14/1.99  --stdin                                 false
% 11.14/1.99  --stats_out                             all
% 11.14/1.99  
% 11.14/1.99  ------ General Options
% 11.14/1.99  
% 11.14/1.99  --fof                                   false
% 11.14/1.99  --time_out_real                         305.
% 11.14/1.99  --time_out_virtual                      -1.
% 11.14/1.99  --symbol_type_check                     false
% 11.14/1.99  --clausify_out                          false
% 11.14/1.99  --sig_cnt_out                           false
% 11.14/1.99  --trig_cnt_out                          false
% 11.14/1.99  --trig_cnt_out_tolerance                1.
% 11.14/1.99  --trig_cnt_out_sk_spl                   false
% 11.14/1.99  --abstr_cl_out                          false
% 11.14/1.99  
% 11.14/1.99  ------ Global Options
% 11.14/1.99  
% 11.14/1.99  --schedule                              default
% 11.14/1.99  --add_important_lit                     false
% 11.14/1.99  --prop_solver_per_cl                    1000
% 11.14/1.99  --min_unsat_core                        false
% 11.14/1.99  --soft_assumptions                      false
% 11.14/1.99  --soft_lemma_size                       3
% 11.14/1.99  --prop_impl_unit_size                   0
% 11.14/1.99  --prop_impl_unit                        []
% 11.14/1.99  --share_sel_clauses                     true
% 11.14/1.99  --reset_solvers                         false
% 11.14/1.99  --bc_imp_inh                            [conj_cone]
% 11.14/1.99  --conj_cone_tolerance                   3.
% 11.14/1.99  --extra_neg_conj                        none
% 11.14/1.99  --large_theory_mode                     true
% 11.14/1.99  --prolific_symb_bound                   200
% 11.14/1.99  --lt_threshold                          2000
% 11.14/1.99  --clause_weak_htbl                      true
% 11.14/1.99  --gc_record_bc_elim                     false
% 11.14/1.99  
% 11.14/1.99  ------ Preprocessing Options
% 11.14/1.99  
% 11.14/1.99  --preprocessing_flag                    true
% 11.14/1.99  --time_out_prep_mult                    0.1
% 11.14/1.99  --splitting_mode                        input
% 11.14/1.99  --splitting_grd                         true
% 11.14/1.99  --splitting_cvd                         false
% 11.14/1.99  --splitting_cvd_svl                     false
% 11.14/1.99  --splitting_nvd                         32
% 11.14/1.99  --sub_typing                            true
% 11.14/1.99  --prep_gs_sim                           true
% 11.14/1.99  --prep_unflatten                        true
% 11.14/1.99  --prep_res_sim                          true
% 11.14/1.99  --prep_upred                            true
% 11.14/1.99  --prep_sem_filter                       exhaustive
% 11.14/1.99  --prep_sem_filter_out                   false
% 11.14/1.99  --pred_elim                             true
% 11.14/1.99  --res_sim_input                         true
% 11.14/1.99  --eq_ax_congr_red                       true
% 11.14/1.99  --pure_diseq_elim                       true
% 11.14/1.99  --brand_transform                       false
% 11.14/1.99  --non_eq_to_eq                          false
% 11.14/1.99  --prep_def_merge                        true
% 11.14/1.99  --prep_def_merge_prop_impl              false
% 11.14/1.99  --prep_def_merge_mbd                    true
% 11.14/1.99  --prep_def_merge_tr_red                 false
% 11.14/1.99  --prep_def_merge_tr_cl                  false
% 11.14/1.99  --smt_preprocessing                     true
% 11.14/1.99  --smt_ac_axioms                         fast
% 11.14/1.99  --preprocessed_out                      false
% 11.14/1.99  --preprocessed_stats                    false
% 11.14/1.99  
% 11.14/1.99  ------ Abstraction refinement Options
% 11.14/1.99  
% 11.14/1.99  --abstr_ref                             []
% 11.14/1.99  --abstr_ref_prep                        false
% 11.14/1.99  --abstr_ref_until_sat                   false
% 11.14/1.99  --abstr_ref_sig_restrict                funpre
% 11.14/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.14/1.99  --abstr_ref_under                       []
% 11.14/1.99  
% 11.14/1.99  ------ SAT Options
% 11.14/1.99  
% 11.14/1.99  --sat_mode                              false
% 11.14/1.99  --sat_fm_restart_options                ""
% 11.14/1.99  --sat_gr_def                            false
% 11.14/1.99  --sat_epr_types                         true
% 11.14/1.99  --sat_non_cyclic_types                  false
% 11.14/1.99  --sat_finite_models                     false
% 11.14/1.99  --sat_fm_lemmas                         false
% 11.14/1.99  --sat_fm_prep                           false
% 11.14/1.99  --sat_fm_uc_incr                        true
% 11.14/1.99  --sat_out_model                         small
% 11.14/1.99  --sat_out_clauses                       false
% 11.14/1.99  
% 11.14/1.99  ------ QBF Options
% 11.14/1.99  
% 11.14/1.99  --qbf_mode                              false
% 11.14/1.99  --qbf_elim_univ                         false
% 11.14/1.99  --qbf_dom_inst                          none
% 11.14/1.99  --qbf_dom_pre_inst                      false
% 11.14/1.99  --qbf_sk_in                             false
% 11.14/1.99  --qbf_pred_elim                         true
% 11.14/1.99  --qbf_split                             512
% 11.14/1.99  
% 11.14/1.99  ------ BMC1 Options
% 11.14/1.99  
% 11.14/1.99  --bmc1_incremental                      false
% 11.14/1.99  --bmc1_axioms                           reachable_all
% 11.14/1.99  --bmc1_min_bound                        0
% 11.14/1.99  --bmc1_max_bound                        -1
% 11.14/1.99  --bmc1_max_bound_default                -1
% 11.14/1.99  --bmc1_symbol_reachability              true
% 11.14/1.99  --bmc1_property_lemmas                  false
% 11.14/1.99  --bmc1_k_induction                      false
% 11.14/1.99  --bmc1_non_equiv_states                 false
% 11.14/1.99  --bmc1_deadlock                         false
% 11.14/1.99  --bmc1_ucm                              false
% 11.14/1.99  --bmc1_add_unsat_core                   none
% 11.14/1.99  --bmc1_unsat_core_children              false
% 11.14/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.14/1.99  --bmc1_out_stat                         full
% 11.14/1.99  --bmc1_ground_init                      false
% 11.14/1.99  --bmc1_pre_inst_next_state              false
% 11.14/1.99  --bmc1_pre_inst_state                   false
% 11.14/1.99  --bmc1_pre_inst_reach_state             false
% 11.14/1.99  --bmc1_out_unsat_core                   false
% 11.14/1.99  --bmc1_aig_witness_out                  false
% 11.14/1.99  --bmc1_verbose                          false
% 11.14/1.99  --bmc1_dump_clauses_tptp                false
% 11.14/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.14/1.99  --bmc1_dump_file                        -
% 11.14/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.14/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.14/1.99  --bmc1_ucm_extend_mode                  1
% 11.14/1.99  --bmc1_ucm_init_mode                    2
% 11.14/1.99  --bmc1_ucm_cone_mode                    none
% 11.14/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.14/1.99  --bmc1_ucm_relax_model                  4
% 11.14/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.14/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.14/1.99  --bmc1_ucm_layered_model                none
% 11.14/1.99  --bmc1_ucm_max_lemma_size               10
% 11.14/1.99  
% 11.14/1.99  ------ AIG Options
% 11.14/1.99  
% 11.14/1.99  --aig_mode                              false
% 11.14/1.99  
% 11.14/1.99  ------ Instantiation Options
% 11.14/1.99  
% 11.14/1.99  --instantiation_flag                    true
% 11.14/1.99  --inst_sos_flag                         true
% 11.14/1.99  --inst_sos_phase                        true
% 11.14/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.14/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.14/1.99  --inst_lit_sel_side                     num_symb
% 11.14/1.99  --inst_solver_per_active                1400
% 11.14/1.99  --inst_solver_calls_frac                1.
% 11.14/1.99  --inst_passive_queue_type               priority_queues
% 11.14/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.14/1.99  --inst_passive_queues_freq              [25;2]
% 11.14/1.99  --inst_dismatching                      true
% 11.14/1.99  --inst_eager_unprocessed_to_passive     true
% 11.14/1.99  --inst_prop_sim_given                   true
% 11.14/1.99  --inst_prop_sim_new                     false
% 11.14/1.99  --inst_subs_new                         false
% 11.14/1.99  --inst_eq_res_simp                      false
% 11.14/1.99  --inst_subs_given                       false
% 11.14/1.99  --inst_orphan_elimination               true
% 11.14/1.99  --inst_learning_loop_flag               true
% 11.14/1.99  --inst_learning_start                   3000
% 11.14/1.99  --inst_learning_factor                  2
% 11.14/1.99  --inst_start_prop_sim_after_learn       3
% 11.14/1.99  --inst_sel_renew                        solver
% 11.14/1.99  --inst_lit_activity_flag                true
% 11.14/1.99  --inst_restr_to_given                   false
% 11.14/1.99  --inst_activity_threshold               500
% 11.14/1.99  --inst_out_proof                        true
% 11.14/1.99  
% 11.14/1.99  ------ Resolution Options
% 11.14/1.99  
% 11.14/1.99  --resolution_flag                       true
% 11.14/1.99  --res_lit_sel                           adaptive
% 11.14/1.99  --res_lit_sel_side                      none
% 11.14/1.99  --res_ordering                          kbo
% 11.14/1.99  --res_to_prop_solver                    active
% 11.14/1.99  --res_prop_simpl_new                    false
% 11.14/1.99  --res_prop_simpl_given                  true
% 11.14/1.99  --res_passive_queue_type                priority_queues
% 11.14/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.14/1.99  --res_passive_queues_freq               [15;5]
% 11.14/1.99  --res_forward_subs                      full
% 11.14/1.99  --res_backward_subs                     full
% 11.14/1.99  --res_forward_subs_resolution           true
% 11.14/1.99  --res_backward_subs_resolution          true
% 11.14/1.99  --res_orphan_elimination                true
% 11.14/1.99  --res_time_limit                        2.
% 11.14/1.99  --res_out_proof                         true
% 11.14/1.99  
% 11.14/1.99  ------ Superposition Options
% 11.14/1.99  
% 11.14/1.99  --superposition_flag                    true
% 11.14/1.99  --sup_passive_queue_type                priority_queues
% 11.14/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.14/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.14/1.99  --demod_completeness_check              fast
% 11.14/1.99  --demod_use_ground                      true
% 11.14/1.99  --sup_to_prop_solver                    passive
% 11.14/1.99  --sup_prop_simpl_new                    true
% 11.14/1.99  --sup_prop_simpl_given                  true
% 11.14/1.99  --sup_fun_splitting                     true
% 11.14/1.99  --sup_smt_interval                      50000
% 11.14/1.99  
% 11.14/1.99  ------ Superposition Simplification Setup
% 11.14/1.99  
% 11.14/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.14/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.14/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.14/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.14/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.14/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.14/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.14/1.99  --sup_immed_triv                        [TrivRules]
% 11.14/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/1.99  --sup_immed_bw_main                     []
% 11.14/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.14/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.14/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/1.99  --sup_input_bw                          []
% 11.14/1.99  
% 11.14/1.99  ------ Combination Options
% 11.14/1.99  
% 11.14/1.99  --comb_res_mult                         3
% 11.14/1.99  --comb_sup_mult                         2
% 11.14/1.99  --comb_inst_mult                        10
% 11.14/1.99  
% 11.14/1.99  ------ Debug Options
% 11.14/1.99  
% 11.14/1.99  --dbg_backtrace                         false
% 11.14/1.99  --dbg_dump_prop_clauses                 false
% 11.14/1.99  --dbg_dump_prop_clauses_file            -
% 11.14/1.99  --dbg_out_stat                          false
% 11.14/1.99  ------ Parsing...
% 11.14/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.14/1.99  
% 11.14/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.14/1.99  
% 11.14/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.14/1.99  
% 11.14/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.14/1.99  ------ Proving...
% 11.14/1.99  ------ Problem Properties 
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  clauses                                 20
% 11.14/1.99  conjectures                             2
% 11.14/1.99  EPR                                     3
% 11.14/1.99  Horn                                    18
% 11.14/1.99  unary                                   7
% 11.14/1.99  binary                                  10
% 11.14/1.99  lits                                    36
% 11.14/1.99  lits eq                                 11
% 11.14/1.99  fd_pure                                 0
% 11.14/1.99  fd_pseudo                               0
% 11.14/1.99  fd_cond                                 0
% 11.14/1.99  fd_pseudo_cond                          3
% 11.14/1.99  AC symbols                              0
% 11.14/1.99  
% 11.14/1.99  ------ Schedule dynamic 5 is on 
% 11.14/1.99  
% 11.14/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  ------ 
% 11.14/1.99  Current options:
% 11.14/1.99  ------ 
% 11.14/1.99  
% 11.14/1.99  ------ Input Options
% 11.14/1.99  
% 11.14/1.99  --out_options                           all
% 11.14/1.99  --tptp_safe_out                         true
% 11.14/1.99  --problem_path                          ""
% 11.14/1.99  --include_path                          ""
% 11.14/1.99  --clausifier                            res/vclausify_rel
% 11.14/1.99  --clausifier_options                    ""
% 11.14/1.99  --stdin                                 false
% 11.14/1.99  --stats_out                             all
% 11.14/1.99  
% 11.14/1.99  ------ General Options
% 11.14/1.99  
% 11.14/1.99  --fof                                   false
% 11.14/1.99  --time_out_real                         305.
% 11.14/1.99  --time_out_virtual                      -1.
% 11.14/1.99  --symbol_type_check                     false
% 11.14/1.99  --clausify_out                          false
% 11.14/1.99  --sig_cnt_out                           false
% 11.14/1.99  --trig_cnt_out                          false
% 11.14/1.99  --trig_cnt_out_tolerance                1.
% 11.14/1.99  --trig_cnt_out_sk_spl                   false
% 11.14/1.99  --abstr_cl_out                          false
% 11.14/1.99  
% 11.14/1.99  ------ Global Options
% 11.14/1.99  
% 11.14/1.99  --schedule                              default
% 11.14/1.99  --add_important_lit                     false
% 11.14/1.99  --prop_solver_per_cl                    1000
% 11.14/1.99  --min_unsat_core                        false
% 11.14/1.99  --soft_assumptions                      false
% 11.14/1.99  --soft_lemma_size                       3
% 11.14/1.99  --prop_impl_unit_size                   0
% 11.14/1.99  --prop_impl_unit                        []
% 11.14/1.99  --share_sel_clauses                     true
% 11.14/1.99  --reset_solvers                         false
% 11.14/1.99  --bc_imp_inh                            [conj_cone]
% 11.14/1.99  --conj_cone_tolerance                   3.
% 11.14/1.99  --extra_neg_conj                        none
% 11.14/1.99  --large_theory_mode                     true
% 11.14/1.99  --prolific_symb_bound                   200
% 11.14/1.99  --lt_threshold                          2000
% 11.14/1.99  --clause_weak_htbl                      true
% 11.14/1.99  --gc_record_bc_elim                     false
% 11.14/1.99  
% 11.14/1.99  ------ Preprocessing Options
% 11.14/1.99  
% 11.14/1.99  --preprocessing_flag                    true
% 11.14/1.99  --time_out_prep_mult                    0.1
% 11.14/1.99  --splitting_mode                        input
% 11.14/1.99  --splitting_grd                         true
% 11.14/1.99  --splitting_cvd                         false
% 11.14/1.99  --splitting_cvd_svl                     false
% 11.14/1.99  --splitting_nvd                         32
% 11.14/1.99  --sub_typing                            true
% 11.14/1.99  --prep_gs_sim                           true
% 11.14/1.99  --prep_unflatten                        true
% 11.14/1.99  --prep_res_sim                          true
% 11.14/1.99  --prep_upred                            true
% 11.14/1.99  --prep_sem_filter                       exhaustive
% 11.14/1.99  --prep_sem_filter_out                   false
% 11.14/1.99  --pred_elim                             true
% 11.14/1.99  --res_sim_input                         true
% 11.14/1.99  --eq_ax_congr_red                       true
% 11.14/1.99  --pure_diseq_elim                       true
% 11.14/1.99  --brand_transform                       false
% 11.14/1.99  --non_eq_to_eq                          false
% 11.14/1.99  --prep_def_merge                        true
% 11.14/1.99  --prep_def_merge_prop_impl              false
% 11.14/1.99  --prep_def_merge_mbd                    true
% 11.14/1.99  --prep_def_merge_tr_red                 false
% 11.14/1.99  --prep_def_merge_tr_cl                  false
% 11.14/1.99  --smt_preprocessing                     true
% 11.14/1.99  --smt_ac_axioms                         fast
% 11.14/1.99  --preprocessed_out                      false
% 11.14/1.99  --preprocessed_stats                    false
% 11.14/1.99  
% 11.14/1.99  ------ Abstraction refinement Options
% 11.14/1.99  
% 11.14/1.99  --abstr_ref                             []
% 11.14/1.99  --abstr_ref_prep                        false
% 11.14/1.99  --abstr_ref_until_sat                   false
% 11.14/1.99  --abstr_ref_sig_restrict                funpre
% 11.14/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.14/1.99  --abstr_ref_under                       []
% 11.14/1.99  
% 11.14/1.99  ------ SAT Options
% 11.14/1.99  
% 11.14/1.99  --sat_mode                              false
% 11.14/1.99  --sat_fm_restart_options                ""
% 11.14/1.99  --sat_gr_def                            false
% 11.14/1.99  --sat_epr_types                         true
% 11.14/1.99  --sat_non_cyclic_types                  false
% 11.14/1.99  --sat_finite_models                     false
% 11.14/1.99  --sat_fm_lemmas                         false
% 11.14/1.99  --sat_fm_prep                           false
% 11.14/1.99  --sat_fm_uc_incr                        true
% 11.14/1.99  --sat_out_model                         small
% 11.14/1.99  --sat_out_clauses                       false
% 11.14/1.99  
% 11.14/1.99  ------ QBF Options
% 11.14/1.99  
% 11.14/1.99  --qbf_mode                              false
% 11.14/1.99  --qbf_elim_univ                         false
% 11.14/1.99  --qbf_dom_inst                          none
% 11.14/1.99  --qbf_dom_pre_inst                      false
% 11.14/1.99  --qbf_sk_in                             false
% 11.14/1.99  --qbf_pred_elim                         true
% 11.14/1.99  --qbf_split                             512
% 11.14/1.99  
% 11.14/1.99  ------ BMC1 Options
% 11.14/1.99  
% 11.14/1.99  --bmc1_incremental                      false
% 11.14/1.99  --bmc1_axioms                           reachable_all
% 11.14/1.99  --bmc1_min_bound                        0
% 11.14/1.99  --bmc1_max_bound                        -1
% 11.14/1.99  --bmc1_max_bound_default                -1
% 11.14/1.99  --bmc1_symbol_reachability              true
% 11.14/1.99  --bmc1_property_lemmas                  false
% 11.14/1.99  --bmc1_k_induction                      false
% 11.14/1.99  --bmc1_non_equiv_states                 false
% 11.14/1.99  --bmc1_deadlock                         false
% 11.14/1.99  --bmc1_ucm                              false
% 11.14/1.99  --bmc1_add_unsat_core                   none
% 11.14/1.99  --bmc1_unsat_core_children              false
% 11.14/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.14/1.99  --bmc1_out_stat                         full
% 11.14/1.99  --bmc1_ground_init                      false
% 11.14/1.99  --bmc1_pre_inst_next_state              false
% 11.14/1.99  --bmc1_pre_inst_state                   false
% 11.14/1.99  --bmc1_pre_inst_reach_state             false
% 11.14/1.99  --bmc1_out_unsat_core                   false
% 11.14/1.99  --bmc1_aig_witness_out                  false
% 11.14/1.99  --bmc1_verbose                          false
% 11.14/1.99  --bmc1_dump_clauses_tptp                false
% 11.14/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.14/1.99  --bmc1_dump_file                        -
% 11.14/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.14/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.14/1.99  --bmc1_ucm_extend_mode                  1
% 11.14/1.99  --bmc1_ucm_init_mode                    2
% 11.14/1.99  --bmc1_ucm_cone_mode                    none
% 11.14/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.14/1.99  --bmc1_ucm_relax_model                  4
% 11.14/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.14/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.14/1.99  --bmc1_ucm_layered_model                none
% 11.14/1.99  --bmc1_ucm_max_lemma_size               10
% 11.14/1.99  
% 11.14/1.99  ------ AIG Options
% 11.14/1.99  
% 11.14/1.99  --aig_mode                              false
% 11.14/1.99  
% 11.14/1.99  ------ Instantiation Options
% 11.14/1.99  
% 11.14/1.99  --instantiation_flag                    true
% 11.14/1.99  --inst_sos_flag                         true
% 11.14/1.99  --inst_sos_phase                        true
% 11.14/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.14/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.14/1.99  --inst_lit_sel_side                     none
% 11.14/1.99  --inst_solver_per_active                1400
% 11.14/1.99  --inst_solver_calls_frac                1.
% 11.14/1.99  --inst_passive_queue_type               priority_queues
% 11.14/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.14/1.99  --inst_passive_queues_freq              [25;2]
% 11.14/1.99  --inst_dismatching                      true
% 11.14/1.99  --inst_eager_unprocessed_to_passive     true
% 11.14/1.99  --inst_prop_sim_given                   true
% 11.14/1.99  --inst_prop_sim_new                     false
% 11.14/1.99  --inst_subs_new                         false
% 11.14/1.99  --inst_eq_res_simp                      false
% 11.14/1.99  --inst_subs_given                       false
% 11.14/1.99  --inst_orphan_elimination               true
% 11.14/1.99  --inst_learning_loop_flag               true
% 11.14/1.99  --inst_learning_start                   3000
% 11.14/1.99  --inst_learning_factor                  2
% 11.14/1.99  --inst_start_prop_sim_after_learn       3
% 11.14/1.99  --inst_sel_renew                        solver
% 11.14/1.99  --inst_lit_activity_flag                true
% 11.14/1.99  --inst_restr_to_given                   false
% 11.14/1.99  --inst_activity_threshold               500
% 11.14/1.99  --inst_out_proof                        true
% 11.14/1.99  
% 11.14/1.99  ------ Resolution Options
% 11.14/1.99  
% 11.14/1.99  --resolution_flag                       false
% 11.14/1.99  --res_lit_sel                           adaptive
% 11.14/1.99  --res_lit_sel_side                      none
% 11.14/1.99  --res_ordering                          kbo
% 11.14/1.99  --res_to_prop_solver                    active
% 11.14/1.99  --res_prop_simpl_new                    false
% 11.14/1.99  --res_prop_simpl_given                  true
% 11.14/1.99  --res_passive_queue_type                priority_queues
% 11.14/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.14/1.99  --res_passive_queues_freq               [15;5]
% 11.14/1.99  --res_forward_subs                      full
% 11.14/1.99  --res_backward_subs                     full
% 11.14/1.99  --res_forward_subs_resolution           true
% 11.14/1.99  --res_backward_subs_resolution          true
% 11.14/1.99  --res_orphan_elimination                true
% 11.14/1.99  --res_time_limit                        2.
% 11.14/1.99  --res_out_proof                         true
% 11.14/1.99  
% 11.14/1.99  ------ Superposition Options
% 11.14/1.99  
% 11.14/1.99  --superposition_flag                    true
% 11.14/1.99  --sup_passive_queue_type                priority_queues
% 11.14/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.14/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.14/1.99  --demod_completeness_check              fast
% 11.14/1.99  --demod_use_ground                      true
% 11.14/1.99  --sup_to_prop_solver                    passive
% 11.14/1.99  --sup_prop_simpl_new                    true
% 11.14/1.99  --sup_prop_simpl_given                  true
% 11.14/1.99  --sup_fun_splitting                     true
% 11.14/1.99  --sup_smt_interval                      50000
% 11.14/1.99  
% 11.14/1.99  ------ Superposition Simplification Setup
% 11.14/1.99  
% 11.14/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.14/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.14/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.14/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.14/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.14/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.14/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.14/1.99  --sup_immed_triv                        [TrivRules]
% 11.14/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/1.99  --sup_immed_bw_main                     []
% 11.14/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.14/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.14/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/1.99  --sup_input_bw                          []
% 11.14/1.99  
% 11.14/1.99  ------ Combination Options
% 11.14/1.99  
% 11.14/1.99  --comb_res_mult                         3
% 11.14/1.99  --comb_sup_mult                         2
% 11.14/1.99  --comb_inst_mult                        10
% 11.14/1.99  
% 11.14/1.99  ------ Debug Options
% 11.14/1.99  
% 11.14/1.99  --dbg_backtrace                         false
% 11.14/1.99  --dbg_dump_prop_clauses                 false
% 11.14/1.99  --dbg_dump_prop_clauses_file            -
% 11.14/1.99  --dbg_out_stat                          false
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  ------ Proving...
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  % SZS status Theorem for theBenchmark.p
% 11.14/1.99  
% 11.14/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.14/1.99  
% 11.14/1.99  fof(f14,conjecture,(
% 11.14/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f15,negated_conjecture,(
% 11.14/1.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.14/1.99    inference(negated_conjecture,[],[f14])).
% 11.14/1.99  
% 11.14/1.99  fof(f22,plain,(
% 11.14/1.99    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.14/1.99    inference(ennf_transformation,[],[f15])).
% 11.14/1.99  
% 11.14/1.99  fof(f30,plain,(
% 11.14/1.99    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.14/1.99    inference(nnf_transformation,[],[f22])).
% 11.14/1.99  
% 11.14/1.99  fof(f31,plain,(
% 11.14/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.14/1.99    inference(flattening,[],[f30])).
% 11.14/1.99  
% 11.14/1.99  fof(f33,plain,(
% 11.14/1.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 11.14/1.99    introduced(choice_axiom,[])).
% 11.14/1.99  
% 11.14/1.99  fof(f32,plain,(
% 11.14/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 11.14/1.99    introduced(choice_axiom,[])).
% 11.14/1.99  
% 11.14/1.99  fof(f34,plain,(
% 11.14/1.99    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.14/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f33,f32])).
% 11.14/1.99  
% 11.14/1.99  fof(f58,plain,(
% 11.14/1.99    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 11.14/1.99    inference(cnf_transformation,[],[f34])).
% 11.14/1.99  
% 11.14/1.99  fof(f12,axiom,(
% 11.14/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f21,plain,(
% 11.14/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.14/1.99    inference(ennf_transformation,[],[f12])).
% 11.14/1.99  
% 11.14/1.99  fof(f54,plain,(
% 11.14/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.14/1.99    inference(cnf_transformation,[],[f21])).
% 11.14/1.99  
% 11.14/1.99  fof(f57,plain,(
% 11.14/1.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 11.14/1.99    inference(cnf_transformation,[],[f34])).
% 11.14/1.99  
% 11.14/1.99  fof(f56,plain,(
% 11.14/1.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.14/1.99    inference(cnf_transformation,[],[f34])).
% 11.14/1.99  
% 11.14/1.99  fof(f8,axiom,(
% 11.14/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f44,plain,(
% 11.14/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.14/1.99    inference(cnf_transformation,[],[f8])).
% 11.14/1.99  
% 11.14/1.99  fof(f5,axiom,(
% 11.14/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f41,plain,(
% 11.14/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f5])).
% 11.14/1.99  
% 11.14/1.99  fof(f4,axiom,(
% 11.14/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f18,plain,(
% 11.14/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.14/1.99    inference(ennf_transformation,[],[f4])).
% 11.14/1.99  
% 11.14/1.99  fof(f40,plain,(
% 11.14/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f18])).
% 11.14/1.99  
% 11.14/1.99  fof(f1,axiom,(
% 11.14/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f35,plain,(
% 11.14/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f1])).
% 11.14/1.99  
% 11.14/1.99  fof(f9,axiom,(
% 11.14/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f45,plain,(
% 11.14/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.14/1.99    inference(cnf_transformation,[],[f9])).
% 11.14/1.99  
% 11.14/1.99  fof(f60,plain,(
% 11.14/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.14/1.99    inference(definition_unfolding,[],[f35,f45,f45])).
% 11.14/1.99  
% 11.14/1.99  fof(f7,axiom,(
% 11.14/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f43,plain,(
% 11.14/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f7])).
% 11.14/1.99  
% 11.14/1.99  fof(f2,axiom,(
% 11.14/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f23,plain,(
% 11.14/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.14/1.99    inference(nnf_transformation,[],[f2])).
% 11.14/1.99  
% 11.14/1.99  fof(f24,plain,(
% 11.14/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.14/1.99    inference(flattening,[],[f23])).
% 11.14/1.99  
% 11.14/1.99  fof(f38,plain,(
% 11.14/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f24])).
% 11.14/1.99  
% 11.14/1.99  fof(f6,axiom,(
% 11.14/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f19,plain,(
% 11.14/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 11.14/1.99    inference(ennf_transformation,[],[f6])).
% 11.14/1.99  
% 11.14/1.99  fof(f42,plain,(
% 11.14/1.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f19])).
% 11.14/1.99  
% 11.14/1.99  fof(f59,plain,(
% 11.14/1.99    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 11.14/1.99    inference(cnf_transformation,[],[f34])).
% 11.14/1.99  
% 11.14/1.99  fof(f3,axiom,(
% 11.14/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f16,plain,(
% 11.14/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 11.14/1.99    inference(pure_predicate_removal,[],[f3])).
% 11.14/1.99  
% 11.14/1.99  fof(f17,plain,(
% 11.14/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.14/1.99    inference(ennf_transformation,[],[f16])).
% 11.14/1.99  
% 11.14/1.99  fof(f39,plain,(
% 11.14/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.14/1.99    inference(cnf_transformation,[],[f17])).
% 11.14/1.99  
% 11.14/1.99  fof(f11,axiom,(
% 11.14/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f20,plain,(
% 11.14/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.14/1.99    inference(ennf_transformation,[],[f11])).
% 11.14/1.99  
% 11.14/1.99  fof(f29,plain,(
% 11.14/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.14/1.99    inference(nnf_transformation,[],[f20])).
% 11.14/1.99  
% 11.14/1.99  fof(f51,plain,(
% 11.14/1.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f29])).
% 11.14/1.99  
% 11.14/1.99  fof(f10,axiom,(
% 11.14/1.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f25,plain,(
% 11.14/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.14/1.99    inference(nnf_transformation,[],[f10])).
% 11.14/1.99  
% 11.14/1.99  fof(f26,plain,(
% 11.14/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.14/1.99    inference(rectify,[],[f25])).
% 11.14/1.99  
% 11.14/1.99  fof(f27,plain,(
% 11.14/1.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.14/1.99    introduced(choice_axiom,[])).
% 11.14/1.99  
% 11.14/1.99  fof(f28,plain,(
% 11.14/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.14/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 11.14/1.99  
% 11.14/1.99  fof(f46,plain,(
% 11.14/1.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.14/1.99    inference(cnf_transformation,[],[f28])).
% 11.14/1.99  
% 11.14/1.99  fof(f64,plain,(
% 11.14/1.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.14/1.99    inference(equality_resolution,[],[f46])).
% 11.14/1.99  
% 11.14/1.99  fof(f47,plain,(
% 11.14/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 11.14/1.99    inference(cnf_transformation,[],[f28])).
% 11.14/1.99  
% 11.14/1.99  fof(f63,plain,(
% 11.14/1.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 11.14/1.99    inference(equality_resolution,[],[f47])).
% 11.14/1.99  
% 11.14/1.99  fof(f13,axiom,(
% 11.14/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.14/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/1.99  
% 11.14/1.99  fof(f55,plain,(
% 11.14/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.14/1.99    inference(cnf_transformation,[],[f13])).
% 11.14/1.99  
% 11.14/1.99  fof(f50,plain,(
% 11.14/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.14/1.99    inference(cnf_transformation,[],[f29])).
% 11.14/1.99  
% 11.14/1.99  cnf(c_21,negated_conjecture,
% 11.14/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.14/1.99      | r1_tarski(sK2,sK3) ),
% 11.14/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1259,plain,
% 11.14/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 11.14/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_18,plain,
% 11.14/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.14/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.14/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_22,negated_conjecture,
% 11.14/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 11.14/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_475,plain,
% 11.14/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.14/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.14/1.99      | sK3 != X1 ),
% 11.14/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_476,plain,
% 11.14/1.99      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 11.14/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.14/1.99      inference(unflattening,[status(thm)],[c_475]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1344,plain,
% 11.14/1.99      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 11.14/1.99      inference(equality_resolution,[status(thm)],[c_476]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_23,negated_conjecture,
% 11.14/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.14/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_484,plain,
% 11.14/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.14/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.14/1.99      | sK2 != X1 ),
% 11.14/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_485,plain,
% 11.14/1.99      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 11.14/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.14/1.99      inference(unflattening,[status(thm)],[c_484]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1345,plain,
% 11.14/1.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 11.14/1.99      inference(equality_resolution,[status(thm)],[c_485]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1442,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 11.14/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.14/1.99      inference(light_normalisation,[status(thm)],[c_1259,c_1344,c_1345]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_9,plain,
% 11.14/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.14/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_6,plain,
% 11.14/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.14/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1267,plain,
% 11.14/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_5,plain,
% 11.14/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.14/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1268,plain,
% 11.14/1.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2467,plain,
% 11.14/1.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1267,c_1268]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3701,plain,
% 11.14/1.99      ( k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_9,c_2467]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3703,plain,
% 11.14/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.14/1.99      inference(light_normalisation,[status(thm)],[c_3701,c_2467]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_0,plain,
% 11.14/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.14/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_8,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.14/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1265,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2112,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_1265]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3803,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_3703,c_2112]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1,plain,
% 11.14/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.14/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1271,plain,
% 11.14/1.99      ( X0 = X1
% 11.14/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.14/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_5465,plain,
% 11.14/1.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1267,c_1271]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_6140,plain,
% 11.14/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_3803,c_5465]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_7,plain,
% 11.14/1.99      ( ~ r1_tarski(X0,X1)
% 11.14/1.99      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 11.14/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1266,plain,
% 11.14/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.14/1.99      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_6399,plain,
% 11.14/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.14/1.99      | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_6140,c_1266]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11233,plain,
% 11.14/1.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 11.14/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_6399,c_5465]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11405,plain,
% 11.14/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = k1_xboole_0
% 11.14/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1442,c_11233]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_20,negated_conjecture,
% 11.14/1.99      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.14/1.99      | ~ r1_tarski(sK2,sK3) ),
% 11.14/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1260,plain,
% 11.14/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 11.14/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1439,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 11.14/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.14/1.99      inference(light_normalisation,[status(thm)],[c_1260,c_1344,c_1345]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_4553,plain,
% 11.14/1.99      ( r1_tarski(sK2,sK3) != iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1266,c_1439]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11510,plain,
% 11.14/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 11.14/1.99      inference(global_propositional_subsumption,
% 11.14/1.99                [status(thm)],
% 11.14/1.99                [c_11405,c_4553]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_4,plain,
% 11.14/1.99      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 11.14/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1269,plain,
% 11.14/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.14/1.99      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2666,plain,
% 11.14/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.14/1.99      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_1269]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_4981,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_2112,c_2666]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11570,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0))),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_11510,c_4981]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11624,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_11570,c_3703]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_16,plain,
% 11.14/1.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.14/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_418,plain,
% 11.14/1.99      ( ~ r2_hidden(X0,X1)
% 11.14/1.99      | v1_xboole_0(X1)
% 11.14/1.99      | X2 != X0
% 11.14/1.99      | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
% 11.14/1.99      | k1_zfmisc_1(X3) != X1 ),
% 11.14/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_419,plain,
% 11.14/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 11.14/1.99      | v1_xboole_0(k1_zfmisc_1(X1))
% 11.14/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.14/1.99      inference(unflattening,[status(thm)],[c_418]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_13,plain,
% 11.14/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.14/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_12,plain,
% 11.14/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.14/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_177,plain,
% 11.14/1.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.14/1.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_178,plain,
% 11.14/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.14/1.99      inference(renaming,[status(thm)],[c_177]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_366,plain,
% 11.14/1.99      ( m1_subset_1(X0,X1)
% 11.14/1.99      | ~ r1_tarski(X2,X3)
% 11.14/1.99      | v1_xboole_0(X1)
% 11.14/1.99      | X0 != X2
% 11.14/1.99      | k1_zfmisc_1(X3) != X1 ),
% 11.14/1.99      inference(resolution_lifted,[status(thm)],[c_178,c_16]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_367,plain,
% 11.14/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.14/1.99      | ~ r1_tarski(X0,X1)
% 11.14/1.99      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 11.14/1.99      inference(unflattening,[status(thm)],[c_366]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_19,plain,
% 11.14/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.14/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_377,plain,
% 11.14/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.14/1.99      inference(forward_subsumption_resolution,
% 11.14/1.99                [status(thm)],
% 11.14/1.99                [c_367,c_19]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_423,plain,
% 11.14/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 11.14/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.14/1.99      inference(global_propositional_subsumption,
% 11.14/1.99                [status(thm)],
% 11.14/1.99                [c_419,c_18,c_13,c_377]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_689,plain,
% 11.14/1.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.14/1.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_690,plain,
% 11.14/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.14/1.99      inference(renaming,[status(thm)],[c_689]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_728,plain,
% 11.14/1.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.14/1.99      inference(bin_hyper_res,[status(thm)],[c_423,c_690]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1256,plain,
% 11.14/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.14/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2114,plain,
% 11.14/1.99      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1265,c_1256]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2394,plain,
% 11.14/1.99      ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_2114]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_4546,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,X1),k3_subset_1(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = iProver_top
% 11.14/1.99      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) != iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_2394,c_1266]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2389,plain,
% 11.14/1.99      ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_2112,c_1256]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_4554,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = iProver_top
% 11.14/1.99      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) != iProver_top ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_4546,c_2389]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1787,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2468,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1265,c_1268]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3449,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.14/1.99      inference(light_normalisation,[status(thm)],[c_1787,c_1787,c_2468]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3454,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_3449]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3580,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X1 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_3454]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_4525,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,X1) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_3580]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_32777,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_4525]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11401,plain,
% 11.14/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1265,c_11233]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_32814,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k1_xboole_0 ),
% 11.14/1.99      inference(light_normalisation,[status(thm)],[c_32777,c_11401]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3809,plain,
% 11.14/1.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_3703,c_0]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2662,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1265,c_1269]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_5129,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),k1_xboole_0) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_3809,c_2662]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_6141,plain,
% 11.14/1.99      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_5129,c_5465]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_6142,plain,
% 11.14/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_6140,c_6141]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_3798,plain,
% 11.14/1.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_3703,c_3454]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_6361,plain,
% 11.14/1.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_6140,c_3798]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_32815,plain,
% 11.14/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_32814,c_9,c_6142,c_6361]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_33132,plain,
% 11.14/1.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_32815,c_3449]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2387,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_0,c_2112]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11407,plain,
% 11.14/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_2387,c_11233]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_33481,plain,
% 11.14/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
% 11.14/1.99      inference(light_normalisation,[status(thm)],[c_33132,c_11407]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_33482,plain,
% 11.14/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_33481,c_2467,c_3703]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_43912,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = iProver_top
% 11.14/1.99      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) != iProver_top ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_4554,c_33482]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_43939,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_11624,c_43912]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_44917,plain,
% 11.14/1.99      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_43939,c_2666]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_17,plain,
% 11.14/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.14/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_457,plain,
% 11.14/1.99      ( r2_hidden(X0,X1)
% 11.14/1.99      | v1_xboole_0(X1)
% 11.14/1.99      | k1_zfmisc_1(sK1) != X1
% 11.14/1.99      | sK2 != X0 ),
% 11.14/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_458,plain,
% 11.14/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.14/1.99      inference(unflattening,[status(thm)],[c_457]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_29,plain,
% 11.14/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.14/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_460,plain,
% 11.14/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 11.14/1.99      inference(global_propositional_subsumption,
% 11.14/1.99                [status(thm)],
% 11.14/1.99                [c_458,c_29]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1257,plain,
% 11.14/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_1261,plain,
% 11.14/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.14/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.14/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_2462,plain,
% 11.14/1.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_1257,c_1261]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_11404,plain,
% 11.14/1.99      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_2462,c_11233]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_12000,plain,
% 11.14/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 11.14/1.99      inference(superposition,[status(thm)],[c_11404,c_0]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_12042,plain,
% 11.14/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 11.14/1.99      inference(demodulation,[status(thm)],[c_12000,c_3703]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(c_44922,plain,
% 11.14/1.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 11.14/1.99      inference(light_normalisation,[status(thm)],[c_44917,c_12042]) ).
% 11.14/1.99  
% 11.14/1.99  cnf(contradiction,plain,
% 11.14/1.99      ( $false ),
% 11.14/1.99      inference(minisat,[status(thm)],[c_44922,c_4553]) ).
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.14/1.99  
% 11.14/1.99  ------                               Statistics
% 11.14/1.99  
% 11.14/1.99  ------ General
% 11.14/1.99  
% 11.14/1.99  abstr_ref_over_cycles:                  0
% 11.14/1.99  abstr_ref_under_cycles:                 0
% 11.14/1.99  gc_basic_clause_elim:                   0
% 11.14/1.99  forced_gc_time:                         0
% 11.14/1.99  parsing_time:                           0.01
% 11.14/1.99  unif_index_cands_time:                  0.
% 11.14/1.99  unif_index_add_time:                    0.
% 11.14/1.99  orderings_time:                         0.
% 11.14/1.99  out_proof_time:                         0.012
% 11.14/1.99  total_time:                             1.255
% 11.14/1.99  num_of_symbols:                         44
% 11.14/1.99  num_of_terms:                           49044
% 11.14/1.99  
% 11.14/1.99  ------ Preprocessing
% 11.14/1.99  
% 11.14/1.99  num_of_splits:                          0
% 11.14/1.99  num_of_split_atoms:                     0
% 11.14/1.99  num_of_reused_defs:                     0
% 11.14/1.99  num_eq_ax_congr_red:                    12
% 11.14/1.99  num_of_sem_filtered_clauses:            1
% 11.14/1.99  num_of_subtypes:                        0
% 11.14/1.99  monotx_restored_types:                  0
% 11.14/1.99  sat_num_of_epr_types:                   0
% 11.14/1.99  sat_num_of_non_cyclic_types:            0
% 11.14/1.99  sat_guarded_non_collapsed_types:        0
% 11.14/1.99  num_pure_diseq_elim:                    0
% 11.14/1.99  simp_replaced_by:                       0
% 11.14/1.99  res_preprocessed:                       100
% 11.14/1.99  prep_upred:                             0
% 11.14/1.99  prep_unflattend:                        46
% 11.14/1.99  smt_new_axioms:                         0
% 11.14/1.99  pred_elim_cands:                        2
% 11.14/1.99  pred_elim:                              2
% 11.14/1.99  pred_elim_cl:                           3
% 11.14/1.99  pred_elim_cycles:                       5
% 11.14/1.99  merged_defs:                            16
% 11.14/1.99  merged_defs_ncl:                        0
% 11.14/1.99  bin_hyper_res:                          17
% 11.14/1.99  prep_cycles:                            4
% 11.14/1.99  pred_elim_time:                         0.007
% 11.14/1.99  splitting_time:                         0.
% 11.14/1.99  sem_filter_time:                        0.
% 11.14/1.99  monotx_time:                            0.001
% 11.14/1.99  subtype_inf_time:                       0.
% 11.14/1.99  
% 11.14/1.99  ------ Problem properties
% 11.14/1.99  
% 11.14/1.99  clauses:                                20
% 11.14/1.99  conjectures:                            2
% 11.14/1.99  epr:                                    3
% 11.14/1.99  horn:                                   18
% 11.14/1.99  ground:                                 4
% 11.14/1.99  unary:                                  7
% 11.14/1.99  binary:                                 10
% 11.14/1.99  lits:                                   36
% 11.14/1.99  lits_eq:                                11
% 11.14/1.99  fd_pure:                                0
% 11.14/1.99  fd_pseudo:                              0
% 11.14/1.99  fd_cond:                                0
% 11.14/1.99  fd_pseudo_cond:                         3
% 11.14/1.99  ac_symbols:                             0
% 11.14/1.99  
% 11.14/1.99  ------ Propositional Solver
% 11.14/1.99  
% 11.14/1.99  prop_solver_calls:                      33
% 11.14/1.99  prop_fast_solver_calls:                 1011
% 11.14/1.99  smt_solver_calls:                       0
% 11.14/1.99  smt_fast_solver_calls:                  0
% 11.14/1.99  prop_num_of_clauses:                    15210
% 11.14/1.99  prop_preprocess_simplified:             23512
% 11.14/1.99  prop_fo_subsumed:                       12
% 11.14/1.99  prop_solver_time:                       0.
% 11.14/1.99  smt_solver_time:                        0.
% 11.14/1.99  smt_fast_solver_time:                   0.
% 11.14/1.99  prop_fast_solver_time:                  0.
% 11.14/1.99  prop_unsat_core_time:                   0.001
% 11.14/1.99  
% 11.14/1.99  ------ QBF
% 11.14/1.99  
% 11.14/1.99  qbf_q_res:                              0
% 11.14/1.99  qbf_num_tautologies:                    0
% 11.14/1.99  qbf_prep_cycles:                        0
% 11.14/1.99  
% 11.14/1.99  ------ BMC1
% 11.14/1.99  
% 11.14/1.99  bmc1_current_bound:                     -1
% 11.14/1.99  bmc1_last_solved_bound:                 -1
% 11.14/1.99  bmc1_unsat_core_size:                   -1
% 11.14/1.99  bmc1_unsat_core_parents_size:           -1
% 11.14/1.99  bmc1_merge_next_fun:                    0
% 11.14/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.14/1.99  
% 11.14/1.99  ------ Instantiation
% 11.14/1.99  
% 11.14/1.99  inst_num_of_clauses:                    3532
% 11.14/1.99  inst_num_in_passive:                    920
% 11.14/1.99  inst_num_in_active:                     1420
% 11.14/1.99  inst_num_in_unprocessed:                1200
% 11.14/1.99  inst_num_of_loops:                      1680
% 11.14/1.99  inst_num_of_learning_restarts:          0
% 11.14/1.99  inst_num_moves_active_passive:          257
% 11.14/1.99  inst_lit_activity:                      0
% 11.14/1.99  inst_lit_activity_moves:                0
% 11.14/1.99  inst_num_tautologies:                   0
% 11.14/1.99  inst_num_prop_implied:                  0
% 11.14/1.99  inst_num_existing_simplified:           0
% 11.14/1.99  inst_num_eq_res_simplified:             0
% 11.14/1.99  inst_num_child_elim:                    0
% 11.14/1.99  inst_num_of_dismatching_blockings:      3393
% 11.14/1.99  inst_num_of_non_proper_insts:           4613
% 11.14/1.99  inst_num_of_duplicates:                 0
% 11.14/1.99  inst_inst_num_from_inst_to_res:         0
% 11.14/1.99  inst_dismatching_checking_time:         0.
% 11.14/1.99  
% 11.14/1.99  ------ Resolution
% 11.14/1.99  
% 11.14/1.99  res_num_of_clauses:                     0
% 11.14/1.99  res_num_in_passive:                     0
% 11.14/1.99  res_num_in_active:                      0
% 11.14/1.99  res_num_of_loops:                       104
% 11.14/1.99  res_forward_subset_subsumed:            333
% 11.14/1.99  res_backward_subset_subsumed:           22
% 11.14/1.99  res_forward_subsumed:                   3
% 11.14/1.99  res_backward_subsumed:                  0
% 11.14/1.99  res_forward_subsumption_resolution:     2
% 11.14/1.99  res_backward_subsumption_resolution:    0
% 11.14/1.99  res_clause_to_clause_subsumption:       39206
% 11.14/1.99  res_orphan_elimination:                 0
% 11.14/1.99  res_tautology_del:                      253
% 11.14/1.99  res_num_eq_res_simplified:              0
% 11.14/1.99  res_num_sel_changes:                    0
% 11.14/1.99  res_moves_from_active_to_pass:          0
% 11.14/1.99  
% 11.14/1.99  ------ Superposition
% 11.14/1.99  
% 11.14/1.99  sup_time_total:                         0.
% 11.14/1.99  sup_time_generating:                    0.
% 11.14/1.99  sup_time_sim_full:                      0.
% 11.14/1.99  sup_time_sim_immed:                     0.
% 11.14/1.99  
% 11.14/1.99  sup_num_of_clauses:                     1490
% 11.14/1.99  sup_num_in_active:                      291
% 11.14/1.99  sup_num_in_passive:                     1199
% 11.14/1.99  sup_num_of_loops:                       334
% 11.14/1.99  sup_fw_superposition:                   5065
% 11.14/1.99  sup_bw_superposition:                   4496
% 11.14/1.99  sup_immediate_simplified:               5270
% 11.14/1.99  sup_given_eliminated:                   19
% 11.14/1.99  comparisons_done:                       0
% 11.14/1.99  comparisons_avoided:                    23
% 11.14/1.99  
% 11.14/1.99  ------ Simplifications
% 11.14/1.99  
% 11.14/1.99  
% 11.14/1.99  sim_fw_subset_subsumed:                 60
% 11.14/1.99  sim_bw_subset_subsumed:                 15
% 11.14/1.99  sim_fw_subsumed:                        1302
% 11.14/1.99  sim_bw_subsumed:                        36
% 11.14/1.99  sim_fw_subsumption_res:                 0
% 11.14/1.99  sim_bw_subsumption_res:                 0
% 11.14/1.99  sim_tautology_del:                      98
% 11.14/1.99  sim_eq_tautology_del:                   1892
% 11.14/1.99  sim_eq_res_simp:                        1
% 11.14/1.99  sim_fw_demodulated:                     4453
% 11.14/1.99  sim_bw_demodulated:                     102
% 11.14/1.99  sim_light_normalised:                   1450
% 11.14/1.99  sim_joinable_taut:                      0
% 11.14/1.99  sim_joinable_simp:                      0
% 11.14/1.99  sim_ac_normalised:                      0
% 11.14/1.99  sim_smt_subsumption:                    0
% 11.14/1.99  
%------------------------------------------------------------------------------
