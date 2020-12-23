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
% DateTime   : Thu Dec  3 11:40:04 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  178 (1875 expanded)
%              Number of clauses        :  122 ( 914 expanded)
%              Number of leaves         :   25 ( 455 expanded)
%              Depth                    :   28
%              Number of atoms          :  423 (5740 expanded)
%              Number of equality atoms :  223 (2636 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK1) != sK2
        | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & ( k2_subset_1(sK1) = sK2
        | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k2_subset_1(sK1) != sK2
      | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & ( k2_subset_1(sK1) = sK2
      | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f33])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f38])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,
    ( k2_subset_1(sK1) != sK2
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_781,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_782,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_781])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_307,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_308,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_314,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_308,c_20])).

cnf(c_959,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_782,c_314])).

cnf(c_960,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_1533,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_1756,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1533])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1544,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5414,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1756,c_1544])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_30450,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_5414,c_0])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) = sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1538,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1572,plain,
    ( sK2 = sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1538,c_18])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1542,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3804,plain,
    ( sK2 = sK1
    | r1_xboole_0(k3_subset_1(sK1,sK2),sK2) != iProver_top
    | v1_xboole_0(k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1542])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_320,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_321,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_1669,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_321])).

cnf(c_7,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1541,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2162,plain,
    ( r1_xboole_0(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1541])).

cnf(c_4440,plain,
    ( sK2 = sK1
    | v1_xboole_0(k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3804,c_2162])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1545,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4446,plain,
    ( k3_subset_1(sK1,sK2) = k1_xboole_0
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_4440,c_1545])).

cnf(c_5411,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_1572,c_1544])).

cnf(c_1699,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1158,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1157,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2420,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1158,c_1157])).

cnf(c_3941,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | sK2 = k2_subset_1(sK1) ),
    inference(resolution,[status(thm)],[c_2420,c_22])).

cnf(c_1162,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4249,plain,
    ( ~ r1_tarski(X0,k2_subset_1(sK1))
    | r1_tarski(X1,sK2)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_3941,c_1162])).

cnf(c_5261,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | r1_tarski(k2_subset_1(sK1),sK2)
    | ~ r1_tarski(sK2,k2_subset_1(sK1)) ),
    inference(resolution,[status(thm)],[c_4249,c_22])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_56,plain,
    ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_66,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_69,plain,
    ( ~ r1_tarski(sK2,sK2)
    | k3_xboole_0(sK2,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1176,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_1628,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | sK2 = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1572])).

cnf(c_1164,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1694,plain,
    ( X0 != sK1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1695,plain,
    ( k1_zfmisc_1(sK2) = k1_zfmisc_1(sK1)
    | sK2 != sK1 ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_1893,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_1829,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k3_subset_1(sK1,sK2) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_1897,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k3_subset_1(sK1,sK2) != k3_subset_1(X0,X1)
    | sK2 != X2 ),
    inference(instantiation,[status(thm)],[c_1829])).

cnf(c_1900,plain,
    ( ~ r1_tarski(k3_subset_1(sK2,sK2),sK2)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_1976,plain,
    ( r1_tarski(sK2,X0)
    | X0 != sK1 ),
    inference(resolution,[status(thm)],[c_1164,c_960])).

cnf(c_1992,plain,
    ( r1_tarski(sK2,k2_subset_1(sK1)) ),
    inference(resolution,[status(thm)],[c_1976,c_18])).

cnf(c_1160,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_2030,plain,
    ( X0 != X1
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k5_xboole_0(X1,X3)
    | k3_xboole_0(X0,X2) != X3 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_2032,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,sK2)
    | k3_xboole_0(sK2,sK2) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_1167,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_2336,plain,
    ( X0 != sK2
    | X1 != sK1
    | k3_subset_1(X1,X0) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_2341,plain,
    ( k3_subset_1(sK2,sK2) = k3_subset_1(sK1,sK2)
    | sK2 != sK2
    | sK2 != sK1 ),
    inference(instantiation,[status(thm)],[c_2336])).

cnf(c_1896,plain,
    ( X0 != X1
    | k3_subset_1(sK1,sK2) != X1
    | k3_subset_1(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_2154,plain,
    ( X0 != k3_subset_1(sK1,sK2)
    | k3_subset_1(sK1,sK2) = X0
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2597,plain,
    ( k3_subset_1(X0,X1) != k3_subset_1(sK1,sK2)
    | k3_subset_1(sK1,sK2) = k3_subset_1(X0,X1)
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_2598,plain,
    ( k3_subset_1(sK2,sK2) != k3_subset_1(sK1,sK2)
    | k3_subset_1(sK1,sK2) = k3_subset_1(sK2,sK2)
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2597])).

cnf(c_1738,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_xboole_0,X2)
    | X1 != X2
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_2865,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X1)
    | ~ r1_tarski(k1_xboole_0,X2)
    | X1 != X2
    | k5_xboole_0(X0,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_2867,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK2),sK2)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | k5_xboole_0(sK2,sK2) != k1_xboole_0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2865])).

cnf(c_2069,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3)
    | X3 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X0 ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_3387,plain,
    ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
    | r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4)
    | X4 != X2
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != k5_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2069])).

cnf(c_3389,plain,
    ( r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK2)
    | ~ r1_tarski(k5_xboole_0(sK2,sK2),sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k5_xboole_0(sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3387])).

cnf(c_4251,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | ~ r1_tarski(sK2,k2_subset_1(sK1))
    | r1_tarski(sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4249])).

cnf(c_3948,plain,
    ( k3_subset_1(X0,sK2) = k5_xboole_0(X0,k3_xboole_0(X0,sK2))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(resolution,[status(thm)],[c_2420,c_321])).

cnf(c_2529,plain,
    ( r1_tarski(X0,k2_subset_1(sK1))
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_1162,c_22])).

cnf(c_5208,plain,
    ( r1_tarski(k3_subset_1(X0,sK2),k2_subset_1(sK1))
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(resolution,[status(thm)],[c_3948,c_2529])).

cnf(c_5211,plain,
    ( r1_tarski(k3_subset_1(sK2,sK2),k2_subset_1(sK1))
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK2)
    | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5208])).

cnf(c_5279,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),k2_subset_1(sK1))
    | r1_tarski(k3_subset_1(X2,X3),sK2)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_4249,c_1167])).

cnf(c_5281,plain,
    ( ~ r1_tarski(k3_subset_1(sK2,sK2),k2_subset_1(sK1))
    | r1_tarski(k3_subset_1(sK2,sK2),sK2)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5279])).

cnf(c_5314,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5261,c_56,c_66,c_69,c_1176,c_1628,c_1695,c_1893,c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,c_4251,c_5211,c_5281])).

cnf(c_6195,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5411,c_56,c_66,c_69,c_1176,c_1628,c_1695,c_1699,c_1893,c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,c_4251,c_5211,c_5281])).

cnf(c_6200,plain,
    ( k3_subset_1(sK1,sK2) = k3_xboole_0(k1_xboole_0,sK2)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_4446,c_6195])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1539,plain,
    ( k2_subset_1(sK1) != sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1581,plain,
    ( sK2 != sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1539,c_18])).

cnf(c_1625,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | sK2 != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1581])).

cnf(c_6358,plain,
    ( k3_subset_1(sK1,sK2) = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6200,c_56,c_66,c_69,c_1176,c_1625,c_1628,c_1695,c_1893,c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,c_4251,c_5211,c_5281])).

cnf(c_6377,plain,
    ( sK2 = sK1
    | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6358,c_1572])).

cnf(c_65,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_67,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_519,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_520,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_521,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_2880,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,X0),X1)
    | ~ r1_tarski(k1_xboole_0,X2)
    | X1 != X2
    | k3_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_2881,plain,
    ( X0 != X1
    | k3_xboole_0(k1_xboole_0,X2) != k1_xboole_0
    | r1_tarski(k3_xboole_0(k1_xboole_0,X2),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2880])).

cnf(c_2883,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) != k1_xboole_0
    | sK2 != sK2
    | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK2) = iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2881])).

cnf(c_6924,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6377,c_67,c_521,c_1176,c_2883])).

cnf(c_6930,plain,
    ( r1_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2) != iProver_top
    | v1_xboole_0(k3_xboole_0(k1_xboole_0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6924,c_1542])).

cnf(c_6367,plain,
    ( sK2 = sK1
    | v1_xboole_0(k3_xboole_0(k1_xboole_0,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6358,c_4440])).

cnf(c_9846,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6930,c_56,c_66,c_69,c_1176,c_1625,c_1628,c_1695,c_1893,c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,c_4251,c_5211,c_5281,c_6367])).

cnf(c_9851,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9846,c_1545])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2463,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_2641,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_2463])).

cnf(c_2687,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1669,c_2641])).

cnf(c_6375,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6358,c_2687])).

cnf(c_10019,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9851,c_6375])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10034,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10019,c_5])).

cnf(c_1631,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_7743,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_1631])).

cnf(c_7877,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_7743,c_5])).

cnf(c_10260,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_10034,c_7877])).

cnf(c_10276,plain,
    ( k3_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_10260,c_5])).

cnf(c_30452,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_30450,c_10276])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30452,c_5314,c_1625])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.91/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.50  
% 7.91/1.50  ------  iProver source info
% 7.91/1.50  
% 7.91/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.50  git: non_committed_changes: false
% 7.91/1.50  git: last_make_outside_of_git: false
% 7.91/1.50  
% 7.91/1.50  ------ 
% 7.91/1.50  ------ Parsing...
% 7.91/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.50  ------ Proving...
% 7.91/1.50  ------ Problem Properties 
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  clauses                                 20
% 7.91/1.50  conjectures                             2
% 7.91/1.50  EPR                                     3
% 7.91/1.50  Horn                                    18
% 7.91/1.50  unary                                   9
% 7.91/1.50  binary                                  7
% 7.91/1.50  lits                                    35
% 7.91/1.50  lits eq                                 18
% 7.91/1.50  fd_pure                                 0
% 7.91/1.50  fd_pseudo                               0
% 7.91/1.50  fd_cond                                 1
% 7.91/1.50  fd_pseudo_cond                          0
% 7.91/1.50  AC symbols                              1
% 7.91/1.50  
% 7.91/1.50  ------ Input Options Time Limit: Unbounded
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  ------ 
% 7.91/1.50  Current options:
% 7.91/1.50  ------ 
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  ------ Proving...
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  % SZS status Theorem for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  fof(f12,axiom,(
% 7.91/1.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f26,plain,(
% 7.91/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.91/1.50    inference(nnf_transformation,[],[f12])).
% 7.91/1.50  
% 7.91/1.50  fof(f27,plain,(
% 7.91/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.91/1.50    inference(rectify,[],[f26])).
% 7.91/1.50  
% 7.91/1.50  fof(f28,plain,(
% 7.91/1.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f29,plain,(
% 7.91/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.91/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 7.91/1.50  
% 7.91/1.50  fof(f46,plain,(
% 7.91/1.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.91/1.50    inference(cnf_transformation,[],[f29])).
% 7.91/1.50  
% 7.91/1.50  fof(f63,plain,(
% 7.91/1.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.91/1.50    inference(equality_resolution,[],[f46])).
% 7.91/1.50  
% 7.91/1.50  fof(f13,axiom,(
% 7.91/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f23,plain,(
% 7.91/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.91/1.50    inference(ennf_transformation,[],[f13])).
% 7.91/1.50  
% 7.91/1.50  fof(f30,plain,(
% 7.91/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.91/1.50    inference(nnf_transformation,[],[f23])).
% 7.91/1.50  
% 7.91/1.50  fof(f50,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f30])).
% 7.91/1.50  
% 7.91/1.50  fof(f17,conjecture,(
% 7.91/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f18,negated_conjecture,(
% 7.91/1.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.91/1.50    inference(negated_conjecture,[],[f17])).
% 7.91/1.50  
% 7.91/1.50  fof(f25,plain,(
% 7.91/1.50    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.50    inference(ennf_transformation,[],[f18])).
% 7.91/1.50  
% 7.91/1.50  fof(f31,plain,(
% 7.91/1.50    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.50    inference(nnf_transformation,[],[f25])).
% 7.91/1.50  
% 7.91/1.50  fof(f32,plain,(
% 7.91/1.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.50    inference(flattening,[],[f31])).
% 7.91/1.50  
% 7.91/1.50  fof(f33,plain,(
% 7.91/1.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f34,plain,(
% 7.91/1.50    (k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.91/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f33])).
% 7.91/1.50  
% 7.91/1.50  fof(f57,plain,(
% 7.91/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.91/1.50    inference(cnf_transformation,[],[f34])).
% 7.91/1.50  
% 7.91/1.50  fof(f16,axiom,(
% 7.91/1.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f56,plain,(
% 7.91/1.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f16])).
% 7.91/1.50  
% 7.91/1.50  fof(f5,axiom,(
% 7.91/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f20,plain,(
% 7.91/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.91/1.50    inference(ennf_transformation,[],[f5])).
% 7.91/1.50  
% 7.91/1.50  fof(f39,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f20])).
% 7.91/1.50  
% 7.91/1.50  fof(f1,axiom,(
% 7.91/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f35,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f1])).
% 7.91/1.50  
% 7.91/1.50  fof(f58,plain,(
% 7.91/1.50    k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 7.91/1.50    inference(cnf_transformation,[],[f34])).
% 7.91/1.50  
% 7.91/1.50  fof(f14,axiom,(
% 7.91/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f54,plain,(
% 7.91/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.91/1.50    inference(cnf_transformation,[],[f14])).
% 7.91/1.50  
% 7.91/1.50  fof(f8,axiom,(
% 7.91/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f21,plain,(
% 7.91/1.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 7.91/1.50    inference(ennf_transformation,[],[f8])).
% 7.91/1.50  
% 7.91/1.50  fof(f22,plain,(
% 7.91/1.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 7.91/1.50    inference(flattening,[],[f21])).
% 7.91/1.50  
% 7.91/1.50  fof(f42,plain,(
% 7.91/1.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f22])).
% 7.91/1.50  
% 7.91/1.50  fof(f15,axiom,(
% 7.91/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f24,plain,(
% 7.91/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.91/1.50    inference(ennf_transformation,[],[f15])).
% 7.91/1.50  
% 7.91/1.50  fof(f55,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f24])).
% 7.91/1.50  
% 7.91/1.50  fof(f4,axiom,(
% 7.91/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f38,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f4])).
% 7.91/1.50  
% 7.91/1.50  fof(f61,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.91/1.50    inference(definition_unfolding,[],[f55,f38])).
% 7.91/1.50  
% 7.91/1.50  fof(f9,axiom,(
% 7.91/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f43,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f9])).
% 7.91/1.50  
% 7.91/1.50  fof(f60,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f43,f38])).
% 7.91/1.50  
% 7.91/1.50  fof(f3,axiom,(
% 7.91/1.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f19,plain,(
% 7.91/1.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.91/1.50    inference(ennf_transformation,[],[f3])).
% 7.91/1.50  
% 7.91/1.50  fof(f37,plain,(
% 7.91/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f19])).
% 7.91/1.50  
% 7.91/1.50  fof(f11,axiom,(
% 7.91/1.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f45,plain,(
% 7.91/1.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.91/1.50    inference(cnf_transformation,[],[f11])).
% 7.91/1.50  
% 7.91/1.50  fof(f6,axiom,(
% 7.91/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f40,plain,(
% 7.91/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f6])).
% 7.91/1.50  
% 7.91/1.50  fof(f59,plain,(
% 7.91/1.50    k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 7.91/1.50    inference(cnf_transformation,[],[f34])).
% 7.91/1.50  
% 7.91/1.50  fof(f2,axiom,(
% 7.91/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f36,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f2])).
% 7.91/1.50  
% 7.91/1.50  fof(f10,axiom,(
% 7.91/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f44,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f10])).
% 7.91/1.50  
% 7.91/1.50  fof(f7,axiom,(
% 7.91/1.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f41,plain,(
% 7.91/1.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.91/1.50    inference(cnf_transformation,[],[f7])).
% 7.91/1.50  
% 7.91/1.50  cnf(c_13,plain,
% 7.91/1.50      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.91/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_781,plain,
% 7.91/1.50      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.91/1.50      inference(prop_impl,[status(thm)],[c_13]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_782,plain,
% 7.91/1.50      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.91/1.50      inference(renaming,[status(thm)],[c_781]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_17,plain,
% 7.91/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.91/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_23,negated_conjecture,
% 7.91/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_307,plain,
% 7.91/1.50      ( r2_hidden(X0,X1)
% 7.91/1.50      | v1_xboole_0(X1)
% 7.91/1.50      | k1_zfmisc_1(sK1) != X1
% 7.91/1.50      | sK2 != X0 ),
% 7.91/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_308,plain,
% 7.91/1.50      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.91/1.50      inference(unflattening,[status(thm)],[c_307]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_20,plain,
% 7.91/1.50      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_314,plain,
% 7.91/1.50      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 7.91/1.50      inference(forward_subsumption_resolution,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_308,c_20]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_959,plain,
% 7.91/1.50      ( r1_tarski(X0,X1)
% 7.91/1.50      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 7.91/1.50      | sK2 != X0 ),
% 7.91/1.50      inference(resolution_lifted,[status(thm)],[c_782,c_314]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_960,plain,
% 7.91/1.50      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.91/1.50      inference(unflattening,[status(thm)],[c_959]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1533,plain,
% 7.91/1.50      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.91/1.50      | r1_tarski(sK2,X0) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1756,plain,
% 7.91/1.50      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.91/1.50      inference(equality_resolution,[status(thm)],[c_1533]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3,plain,
% 7.91/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1544,plain,
% 7.91/1.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5414,plain,
% 7.91/1.50      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1756,c_1544]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_0,plain,
% 7.91/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_30450,plain,
% 7.91/1.50      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_5414,c_0]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_22,negated_conjecture,
% 7.91/1.50      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) = sK2 ),
% 7.91/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1538,plain,
% 7.91/1.50      ( k2_subset_1(sK1) = sK2
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_18,plain,
% 7.91/1.50      ( k2_subset_1(X0) = X0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1572,plain,
% 7.91/1.50      ( sK2 = sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_1538,c_18]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6,plain,
% 7.91/1.50      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1542,plain,
% 7.91/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.91/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.91/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3804,plain,
% 7.91/1.50      ( sK2 = sK1
% 7.91/1.50      | r1_xboole_0(k3_subset_1(sK1,sK2),sK2) != iProver_top
% 7.91/1.50      | v1_xboole_0(k3_subset_1(sK1,sK2)) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1572,c_1542]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_19,plain,
% 7.91/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.50      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_320,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.91/1.50      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.91/1.50      | sK2 != X1 ),
% 7.91/1.50      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_321,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
% 7.91/1.50      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.91/1.50      inference(unflattening,[status(thm)],[c_320]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1669,plain,
% 7.91/1.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(equality_resolution,[status(thm)],[c_321]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7,plain,
% 7.91/1.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 7.91/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1541,plain,
% 7.91/1.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2162,plain,
% 7.91/1.50      ( r1_xboole_0(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1669,c_1541]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4440,plain,
% 7.91/1.50      ( sK2 = sK1 | v1_xboole_0(k3_subset_1(sK1,sK2)) = iProver_top ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_3804,c_2162]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2,plain,
% 7.91/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1545,plain,
% 7.91/1.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4446,plain,
% 7.91/1.50      ( k3_subset_1(sK1,sK2) = k1_xboole_0 | sK2 = sK1 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_4440,c_1545]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5411,plain,
% 7.91/1.50      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
% 7.91/1.50      | sK2 = sK1 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1572,c_1544]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1699,plain,
% 7.91/1.50      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1158,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1157,plain,( X0 = X0 ),theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2420,plain,
% 7.91/1.50      ( X0 != X1 | X1 = X0 ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_1158,c_1157]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3941,plain,
% 7.91/1.50      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | sK2 = k2_subset_1(sK1) ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_2420,c_22]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1162,plain,
% 7.91/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.91/1.50      theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4249,plain,
% 7.91/1.50      ( ~ r1_tarski(X0,k2_subset_1(sK1))
% 7.91/1.50      | r1_tarski(X1,sK2)
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | X1 != X0 ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_3941,c_1162]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5261,plain,
% 7.91/1.50      ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | r1_tarski(k2_subset_1(sK1),sK2)
% 7.91/1.50      | ~ r1_tarski(sK2,k2_subset_1(sK1)) ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_4249,c_22]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9,plain,
% 7.91/1.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_56,plain,
% 7.91/1.50      ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4,plain,
% 7.91/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_66,plain,
% 7.91/1.50      ( r1_tarski(k1_xboole_0,sK2) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_69,plain,
% 7.91/1.50      ( ~ r1_tarski(sK2,sK2) | k3_xboole_0(sK2,sK2) = sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1176,plain,
% 7.91/1.50      ( sK2 = sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1157]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1628,plain,
% 7.91/1.50      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | sK2 = sK1 ),
% 7.91/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1572]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1164,plain,
% 7.91/1.50      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.91/1.50      theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1694,plain,
% 7.91/1.50      ( X0 != sK1 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK1) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1164]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1695,plain,
% 7.91/1.50      ( k1_zfmisc_1(sK2) = k1_zfmisc_1(sK1) | sK2 != sK1 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1694]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1893,plain,
% 7.91/1.50      ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1157]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1829,plain,
% 7.91/1.50      ( ~ r1_tarski(X0,X1)
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | k3_subset_1(sK1,sK2) != X0
% 7.91/1.50      | sK2 != X1 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1162]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1897,plain,
% 7.91/1.50      ( ~ r1_tarski(k3_subset_1(X0,X1),X2)
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | k3_subset_1(sK1,sK2) != k3_subset_1(X0,X1)
% 7.91/1.50      | sK2 != X2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1829]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1900,plain,
% 7.91/1.50      ( ~ r1_tarski(k3_subset_1(sK2,sK2),sK2)
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK2,sK2)
% 7.91/1.50      | sK2 != sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1897]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1976,plain,
% 7.91/1.50      ( r1_tarski(sK2,X0) | X0 != sK1 ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_1164,c_960]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1992,plain,
% 7.91/1.50      ( r1_tarski(sK2,k2_subset_1(sK1)) ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_1976,c_18]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1160,plain,
% 7.91/1.50      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 7.91/1.50      theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2030,plain,
% 7.91/1.50      ( X0 != X1
% 7.91/1.50      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k5_xboole_0(X1,X3)
% 7.91/1.50      | k3_xboole_0(X0,X2) != X3 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1160]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2032,plain,
% 7.91/1.50      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,sK2)
% 7.91/1.50      | k3_xboole_0(sK2,sK2) != sK2
% 7.91/1.50      | sK2 != sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2030]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1167,plain,
% 7.91/1.50      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 7.91/1.50      theory(equality) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2336,plain,
% 7.91/1.50      ( X0 != sK2
% 7.91/1.50      | X1 != sK1
% 7.91/1.50      | k3_subset_1(X1,X0) = k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1167]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2341,plain,
% 7.91/1.50      ( k3_subset_1(sK2,sK2) = k3_subset_1(sK1,sK2)
% 7.91/1.50      | sK2 != sK2
% 7.91/1.50      | sK2 != sK1 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2336]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1896,plain,
% 7.91/1.50      ( X0 != X1
% 7.91/1.50      | k3_subset_1(sK1,sK2) != X1
% 7.91/1.50      | k3_subset_1(sK1,sK2) = X0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1158]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2154,plain,
% 7.91/1.50      ( X0 != k3_subset_1(sK1,sK2)
% 7.91/1.50      | k3_subset_1(sK1,sK2) = X0
% 7.91/1.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1896]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2597,plain,
% 7.91/1.50      ( k3_subset_1(X0,X1) != k3_subset_1(sK1,sK2)
% 7.91/1.50      | k3_subset_1(sK1,sK2) = k3_subset_1(X0,X1)
% 7.91/1.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2154]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2598,plain,
% 7.91/1.50      ( k3_subset_1(sK2,sK2) != k3_subset_1(sK1,sK2)
% 7.91/1.50      | k3_subset_1(sK1,sK2) = k3_subset_1(sK2,sK2)
% 7.91/1.50      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2597]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1738,plain,
% 7.91/1.50      ( r1_tarski(X0,X1)
% 7.91/1.50      | ~ r1_tarski(k1_xboole_0,X2)
% 7.91/1.50      | X1 != X2
% 7.91/1.50      | X0 != k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1162]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2865,plain,
% 7.91/1.50      ( r1_tarski(k5_xboole_0(X0,X0),X1)
% 7.91/1.50      | ~ r1_tarski(k1_xboole_0,X2)
% 7.91/1.50      | X1 != X2
% 7.91/1.50      | k5_xboole_0(X0,X0) != k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1738]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2867,plain,
% 7.91/1.50      ( r1_tarski(k5_xboole_0(sK2,sK2),sK2)
% 7.91/1.50      | ~ r1_tarski(k1_xboole_0,sK2)
% 7.91/1.50      | k5_xboole_0(sK2,sK2) != k1_xboole_0
% 7.91/1.50      | sK2 != sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2865]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2069,plain,
% 7.91/1.50      ( ~ r1_tarski(X0,X1)
% 7.91/1.50      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3)
% 7.91/1.50      | X3 != X1
% 7.91/1.50      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1162]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3387,plain,
% 7.91/1.50      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
% 7.91/1.50      | r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4)
% 7.91/1.50      | X4 != X2
% 7.91/1.50      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != k5_xboole_0(X0,X1) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2069]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3389,plain,
% 7.91/1.50      ( r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK2)
% 7.91/1.50      | ~ r1_tarski(k5_xboole_0(sK2,sK2),sK2)
% 7.91/1.50      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k5_xboole_0(sK2,sK2)
% 7.91/1.50      | sK2 != sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_3387]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4251,plain,
% 7.91/1.50      ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | ~ r1_tarski(sK2,k2_subset_1(sK1))
% 7.91/1.50      | r1_tarski(sK2,sK2)
% 7.91/1.50      | sK2 != sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_4249]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3948,plain,
% 7.91/1.50      ( k3_subset_1(X0,sK2) = k5_xboole_0(X0,k3_xboole_0(X0,sK2))
% 7.91/1.50      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_2420,c_321]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2529,plain,
% 7.91/1.50      ( r1_tarski(X0,k2_subset_1(sK1))
% 7.91/1.50      | ~ r1_tarski(X1,sK2)
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | X0 != X1 ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_1162,c_22]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5208,plain,
% 7.91/1.50      ( r1_tarski(k3_subset_1(X0,sK2),k2_subset_1(sK1))
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,sK2)),sK2)
% 7.91/1.50      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_3948,c_2529]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5211,plain,
% 7.91/1.50      ( r1_tarski(k3_subset_1(sK2,sK2),k2_subset_1(sK1))
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK2)
% 7.91/1.50      | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK1) ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_5208]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5279,plain,
% 7.91/1.50      ( ~ r1_tarski(k3_subset_1(X0,X1),k2_subset_1(sK1))
% 7.91/1.50      | r1_tarski(k3_subset_1(X2,X3),sK2)
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | X2 != X0
% 7.91/1.50      | X3 != X1 ),
% 7.91/1.50      inference(resolution,[status(thm)],[c_4249,c_1167]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5281,plain,
% 7.91/1.50      ( ~ r1_tarski(k3_subset_1(sK2,sK2),k2_subset_1(sK1))
% 7.91/1.50      | r1_tarski(k3_subset_1(sK2,sK2),sK2)
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2)
% 7.91/1.50      | sK2 != sK2 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_5279]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5314,plain,
% 7.91/1.50      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_5261,c_56,c_66,c_69,c_1176,c_1628,c_1695,c_1893,
% 7.91/1.50                 c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,c_4251,
% 7.91/1.50                 c_5211,c_5281]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6195,plain,
% 7.91/1.50      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2) ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_5411,c_56,c_66,c_69,c_1176,c_1628,c_1695,c_1699,
% 7.91/1.50                 c_1893,c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,
% 7.91/1.50                 c_4251,c_5211,c_5281]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6200,plain,
% 7.91/1.50      ( k3_subset_1(sK1,sK2) = k3_xboole_0(k1_xboole_0,sK2) | sK2 = sK1 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_4446,c_6195]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_21,negated_conjecture,
% 7.91/1.50      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) != sK2 ),
% 7.91/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1539,plain,
% 7.91/1.50      ( k2_subset_1(sK1) != sK2
% 7.91/1.50      | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1581,plain,
% 7.91/1.50      ( sK2 != sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_1539,c_18]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1625,plain,
% 7.91/1.50      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | sK2 != sK1 ),
% 7.91/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1581]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6358,plain,
% 7.91/1.50      ( k3_subset_1(sK1,sK2) = k3_xboole_0(k1_xboole_0,sK2) ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_6200,c_56,c_66,c_69,c_1176,c_1625,c_1628,c_1695,
% 7.91/1.50                 c_1893,c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,
% 7.91/1.50                 c_4251,c_5211,c_5281]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6377,plain,
% 7.91/1.50      ( sK2 = sK1
% 7.91/1.50      | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK2) = iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_6358,c_1572]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_65,plain,
% 7.91/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_67,plain,
% 7.91/1.50      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_65]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_519,plain,
% 7.91/1.50      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 7.91/1.50      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_520,plain,
% 7.91/1.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.91/1.50      inference(unflattening,[status(thm)],[c_519]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_521,plain,
% 7.91/1.50      ( k3_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_520]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2880,plain,
% 7.91/1.50      ( r1_tarski(k3_xboole_0(k1_xboole_0,X0),X1)
% 7.91/1.50      | ~ r1_tarski(k1_xboole_0,X2)
% 7.91/1.50      | X1 != X2
% 7.91/1.50      | k3_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_1738]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2881,plain,
% 7.91/1.50      ( X0 != X1
% 7.91/1.50      | k3_xboole_0(k1_xboole_0,X2) != k1_xboole_0
% 7.91/1.50      | r1_tarski(k3_xboole_0(k1_xboole_0,X2),X0) = iProver_top
% 7.91/1.50      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_2880]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2883,plain,
% 7.91/1.50      ( k3_xboole_0(k1_xboole_0,sK2) != k1_xboole_0
% 7.91/1.50      | sK2 != sK2
% 7.91/1.50      | r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK2) = iProver_top
% 7.91/1.50      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2881]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6924,plain,
% 7.91/1.50      ( r1_tarski(k3_xboole_0(k1_xboole_0,sK2),sK2) = iProver_top ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_6377,c_67,c_521,c_1176,c_2883]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6930,plain,
% 7.91/1.50      ( r1_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2) != iProver_top
% 7.91/1.50      | v1_xboole_0(k3_xboole_0(k1_xboole_0,sK2)) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_6924,c_1542]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6367,plain,
% 7.91/1.50      ( sK2 = sK1
% 7.91/1.50      | v1_xboole_0(k3_xboole_0(k1_xboole_0,sK2)) = iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_6358,c_4440]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9846,plain,
% 7.91/1.50      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,sK2)) = iProver_top ),
% 7.91/1.50      inference(global_propositional_subsumption,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_6930,c_56,c_66,c_69,c_1176,c_1625,c_1628,c_1695,
% 7.91/1.50                 c_1893,c_1900,c_1992,c_2032,c_2341,c_2598,c_2867,c_3389,
% 7.91/1.50                 c_4251,c_5211,c_5281,c_6367]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9851,plain,
% 7.91/1.50      ( k3_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_9846,c_1545]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1,plain,
% 7.91/1.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_8,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2463,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2641,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1,c_2463]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2687,plain,
% 7.91/1.50      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1669,c_2641]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6375,plain,
% 7.91/1.50      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k1_xboole_0 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_6358,c_2687]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10019,plain,
% 7.91/1.50      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_9851,c_6375]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10034,plain,
% 7.91/1.50      ( k5_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k1_xboole_0 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_10019,c_5]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1631,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7743,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_9,c_1631]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_7877,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_7743,c_5]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10260,plain,
% 7.91/1.50      ( k5_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK2) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_10034,c_7877]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10276,plain,
% 7.91/1.50      ( k3_xboole_0(sK1,sK2) = sK1 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_10260,c_5]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_30452,plain,
% 7.91/1.50      ( sK2 = sK1 ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_30450,c_10276]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(contradiction,plain,
% 7.91/1.50      ( $false ),
% 7.91/1.50      inference(minisat,[status(thm)],[c_30452,c_5314,c_1625]) ).
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  ------                               Statistics
% 7.91/1.50  
% 7.91/1.50  ------ Selected
% 7.91/1.50  
% 7.91/1.50  total_time:                             0.725
% 7.91/1.50  
%------------------------------------------------------------------------------
