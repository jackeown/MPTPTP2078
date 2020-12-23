%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:32 EST 2020

% Result     : Theorem 11.89s
% Output     : CNFRefutation 11.89s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 707 expanded)
%              Number of clauses        :   76 ( 245 expanded)
%              Number of leaves         :   19 ( 154 expanded)
%              Depth                    :   21
%              Number of atoms          :  355 (2570 expanded)
%              Number of equality atoms :  125 ( 437 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f40,f39])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f48])).

fof(f69,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f48,f48])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_482,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_483,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_485,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_33])).

cnf(c_1391,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1394,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2847,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_1394])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1400,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3164,plain,
    ( k3_xboole_0(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_2847,c_1400])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4539,plain,
    ( k3_xboole_0(sK1,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3164,c_1])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_518,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_519,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_1519,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_519])).

cnf(c_4780,plain,
    ( k3_subset_1(sK1,sK3) = k5_xboole_0(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_4539,c_1519])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1392,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4996,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4780,c_1392])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_527,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_528,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_1520,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_528])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1404,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4788,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_1404])).

cnf(c_5241,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(k5_xboole_0(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4996,c_4788])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1407,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5351,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(sK2,k5_xboole_0(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5241,c_1407])).

cnf(c_500,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_501,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_503,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_33])).

cnf(c_1390,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_2848,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1394])).

cnf(c_3341,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_2848,c_1400])).

cnf(c_7155,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3341,c_1])).

cnf(c_7602,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_7155,c_1520])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1393,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4997,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4780,c_1393])).

cnf(c_7807,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k5_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7602,c_4997])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1399,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6178,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_1399])).

cnf(c_6527,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4539,c_6178])).

cnf(c_8027,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7807,c_4997,c_6527])).

cnf(c_11749,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5351,c_4997,c_6527])).

cnf(c_12,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1398,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7381,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1398])).

cnf(c_11981,plain,
    ( r1_tarski(X0,k2_xboole_0(sK3,sK1)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | r1_xboole_0(X0,k5_xboole_0(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4539,c_7381])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1401,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3163,plain,
    ( k2_xboole_0(sK3,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2847,c_1401])).

cnf(c_11989,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(sK1,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11981,c_3163])).

cnf(c_46217,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11749,c_11989])).

cnf(c_955,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_960,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_203,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_204,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_641,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_503])).

cnf(c_642,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_643,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_645,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_87,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_83,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46217,c_8027,c_960,c_645,c_87,c_83])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.89/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.89/1.99  
% 11.89/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.89/1.99  
% 11.89/1.99  ------  iProver source info
% 11.89/1.99  
% 11.89/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.89/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.89/1.99  git: non_committed_changes: false
% 11.89/1.99  git: last_make_outside_of_git: false
% 11.89/1.99  
% 11.89/1.99  ------ 
% 11.89/1.99  
% 11.89/1.99  ------ Input Options
% 11.89/1.99  
% 11.89/1.99  --out_options                           all
% 11.89/1.99  --tptp_safe_out                         true
% 11.89/1.99  --problem_path                          ""
% 11.89/1.99  --include_path                          ""
% 11.89/1.99  --clausifier                            res/vclausify_rel
% 11.89/1.99  --clausifier_options                    ""
% 11.89/1.99  --stdin                                 false
% 11.89/1.99  --stats_out                             all
% 11.89/1.99  
% 11.89/1.99  ------ General Options
% 11.89/1.99  
% 11.89/1.99  --fof                                   false
% 11.89/1.99  --time_out_real                         305.
% 11.89/1.99  --time_out_virtual                      -1.
% 11.89/1.99  --symbol_type_check                     false
% 11.89/1.99  --clausify_out                          false
% 11.89/1.99  --sig_cnt_out                           false
% 11.89/1.99  --trig_cnt_out                          false
% 11.89/1.99  --trig_cnt_out_tolerance                1.
% 11.89/1.99  --trig_cnt_out_sk_spl                   false
% 11.89/1.99  --abstr_cl_out                          false
% 11.89/1.99  
% 11.89/1.99  ------ Global Options
% 11.89/1.99  
% 11.89/1.99  --schedule                              default
% 11.89/1.99  --add_important_lit                     false
% 11.89/1.99  --prop_solver_per_cl                    1000
% 11.89/1.99  --min_unsat_core                        false
% 11.89/1.99  --soft_assumptions                      false
% 11.89/1.99  --soft_lemma_size                       3
% 11.89/1.99  --prop_impl_unit_size                   0
% 11.89/1.99  --prop_impl_unit                        []
% 11.89/1.99  --share_sel_clauses                     true
% 11.89/1.99  --reset_solvers                         false
% 11.89/1.99  --bc_imp_inh                            [conj_cone]
% 11.89/1.99  --conj_cone_tolerance                   3.
% 11.89/1.99  --extra_neg_conj                        none
% 11.89/1.99  --large_theory_mode                     true
% 11.89/1.99  --prolific_symb_bound                   200
% 11.89/1.99  --lt_threshold                          2000
% 11.89/1.99  --clause_weak_htbl                      true
% 11.89/1.99  --gc_record_bc_elim                     false
% 11.89/1.99  
% 11.89/1.99  ------ Preprocessing Options
% 11.89/1.99  
% 11.89/1.99  --preprocessing_flag                    true
% 11.89/1.99  --time_out_prep_mult                    0.1
% 11.89/1.99  --splitting_mode                        input
% 11.89/1.99  --splitting_grd                         true
% 11.89/1.99  --splitting_cvd                         false
% 11.89/1.99  --splitting_cvd_svl                     false
% 11.89/1.99  --splitting_nvd                         32
% 11.89/1.99  --sub_typing                            true
% 11.89/1.99  --prep_gs_sim                           true
% 11.89/1.99  --prep_unflatten                        true
% 11.89/1.99  --prep_res_sim                          true
% 11.89/1.99  --prep_upred                            true
% 11.89/1.99  --prep_sem_filter                       exhaustive
% 11.89/1.99  --prep_sem_filter_out                   false
% 11.89/1.99  --pred_elim                             true
% 11.89/1.99  --res_sim_input                         true
% 11.89/1.99  --eq_ax_congr_red                       true
% 11.89/1.99  --pure_diseq_elim                       true
% 11.89/1.99  --brand_transform                       false
% 11.89/1.99  --non_eq_to_eq                          false
% 11.89/1.99  --prep_def_merge                        true
% 11.89/1.99  --prep_def_merge_prop_impl              false
% 11.89/1.99  --prep_def_merge_mbd                    true
% 11.89/1.99  --prep_def_merge_tr_red                 false
% 11.89/1.99  --prep_def_merge_tr_cl                  false
% 11.89/1.99  --smt_preprocessing                     true
% 11.89/1.99  --smt_ac_axioms                         fast
% 11.89/1.99  --preprocessed_out                      false
% 11.89/1.99  --preprocessed_stats                    false
% 11.89/1.99  
% 11.89/1.99  ------ Abstraction refinement Options
% 11.89/1.99  
% 11.89/1.99  --abstr_ref                             []
% 11.89/1.99  --abstr_ref_prep                        false
% 11.89/1.99  --abstr_ref_until_sat                   false
% 11.89/1.99  --abstr_ref_sig_restrict                funpre
% 11.89/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.89/1.99  --abstr_ref_under                       []
% 11.89/1.99  
% 11.89/1.99  ------ SAT Options
% 11.89/1.99  
% 11.89/1.99  --sat_mode                              false
% 11.89/1.99  --sat_fm_restart_options                ""
% 11.89/1.99  --sat_gr_def                            false
% 11.89/1.99  --sat_epr_types                         true
% 11.89/1.99  --sat_non_cyclic_types                  false
% 11.89/1.99  --sat_finite_models                     false
% 11.89/1.99  --sat_fm_lemmas                         false
% 11.89/1.99  --sat_fm_prep                           false
% 11.89/1.99  --sat_fm_uc_incr                        true
% 11.89/1.99  --sat_out_model                         small
% 11.89/1.99  --sat_out_clauses                       false
% 11.89/1.99  
% 11.89/1.99  ------ QBF Options
% 11.89/1.99  
% 11.89/1.99  --qbf_mode                              false
% 11.89/1.99  --qbf_elim_univ                         false
% 11.89/1.99  --qbf_dom_inst                          none
% 11.89/1.99  --qbf_dom_pre_inst                      false
% 11.89/1.99  --qbf_sk_in                             false
% 11.89/1.99  --qbf_pred_elim                         true
% 11.89/1.99  --qbf_split                             512
% 11.89/1.99  
% 11.89/1.99  ------ BMC1 Options
% 11.89/1.99  
% 11.89/1.99  --bmc1_incremental                      false
% 11.89/1.99  --bmc1_axioms                           reachable_all
% 11.89/1.99  --bmc1_min_bound                        0
% 11.89/1.99  --bmc1_max_bound                        -1
% 11.89/1.99  --bmc1_max_bound_default                -1
% 11.89/1.99  --bmc1_symbol_reachability              true
% 11.89/1.99  --bmc1_property_lemmas                  false
% 11.89/1.99  --bmc1_k_induction                      false
% 11.89/1.99  --bmc1_non_equiv_states                 false
% 11.89/1.99  --bmc1_deadlock                         false
% 11.89/1.99  --bmc1_ucm                              false
% 11.89/1.99  --bmc1_add_unsat_core                   none
% 11.89/1.99  --bmc1_unsat_core_children              false
% 11.89/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.89/1.99  --bmc1_out_stat                         full
% 11.89/1.99  --bmc1_ground_init                      false
% 11.89/1.99  --bmc1_pre_inst_next_state              false
% 11.89/1.99  --bmc1_pre_inst_state                   false
% 11.89/1.99  --bmc1_pre_inst_reach_state             false
% 11.89/1.99  --bmc1_out_unsat_core                   false
% 11.89/1.99  --bmc1_aig_witness_out                  false
% 11.89/1.99  --bmc1_verbose                          false
% 11.89/1.99  --bmc1_dump_clauses_tptp                false
% 11.89/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.89/1.99  --bmc1_dump_file                        -
% 11.89/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.89/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.89/1.99  --bmc1_ucm_extend_mode                  1
% 11.89/1.99  --bmc1_ucm_init_mode                    2
% 11.89/1.99  --bmc1_ucm_cone_mode                    none
% 11.89/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.89/1.99  --bmc1_ucm_relax_model                  4
% 11.89/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.89/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.89/1.99  --bmc1_ucm_layered_model                none
% 11.89/1.99  --bmc1_ucm_max_lemma_size               10
% 11.89/1.99  
% 11.89/1.99  ------ AIG Options
% 11.89/1.99  
% 11.89/1.99  --aig_mode                              false
% 11.89/1.99  
% 11.89/1.99  ------ Instantiation Options
% 11.89/1.99  
% 11.89/1.99  --instantiation_flag                    true
% 11.89/1.99  --inst_sos_flag                         true
% 11.89/1.99  --inst_sos_phase                        true
% 11.89/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.89/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.89/1.99  --inst_lit_sel_side                     num_symb
% 11.89/1.99  --inst_solver_per_active                1400
% 11.89/1.99  --inst_solver_calls_frac                1.
% 11.89/1.99  --inst_passive_queue_type               priority_queues
% 11.89/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.89/1.99  --inst_passive_queues_freq              [25;2]
% 11.89/1.99  --inst_dismatching                      true
% 11.89/1.99  --inst_eager_unprocessed_to_passive     true
% 11.89/1.99  --inst_prop_sim_given                   true
% 11.89/1.99  --inst_prop_sim_new                     false
% 11.89/1.99  --inst_subs_new                         false
% 11.89/1.99  --inst_eq_res_simp                      false
% 11.89/1.99  --inst_subs_given                       false
% 11.89/1.99  --inst_orphan_elimination               true
% 11.89/1.99  --inst_learning_loop_flag               true
% 11.89/1.99  --inst_learning_start                   3000
% 11.89/1.99  --inst_learning_factor                  2
% 11.89/1.99  --inst_start_prop_sim_after_learn       3
% 11.89/1.99  --inst_sel_renew                        solver
% 11.89/1.99  --inst_lit_activity_flag                true
% 11.89/1.99  --inst_restr_to_given                   false
% 11.89/1.99  --inst_activity_threshold               500
% 11.89/1.99  --inst_out_proof                        true
% 11.89/1.99  
% 11.89/1.99  ------ Resolution Options
% 11.89/1.99  
% 11.89/1.99  --resolution_flag                       true
% 11.89/1.99  --res_lit_sel                           adaptive
% 11.89/1.99  --res_lit_sel_side                      none
% 11.89/1.99  --res_ordering                          kbo
% 11.89/1.99  --res_to_prop_solver                    active
% 11.89/1.99  --res_prop_simpl_new                    false
% 11.89/1.99  --res_prop_simpl_given                  true
% 11.89/1.99  --res_passive_queue_type                priority_queues
% 11.89/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.89/1.99  --res_passive_queues_freq               [15;5]
% 11.89/1.99  --res_forward_subs                      full
% 11.89/1.99  --res_backward_subs                     full
% 11.89/1.99  --res_forward_subs_resolution           true
% 11.89/1.99  --res_backward_subs_resolution          true
% 11.89/1.99  --res_orphan_elimination                true
% 11.89/1.99  --res_time_limit                        2.
% 11.89/1.99  --res_out_proof                         true
% 11.89/1.99  
% 11.89/1.99  ------ Superposition Options
% 11.89/1.99  
% 11.89/1.99  --superposition_flag                    true
% 11.89/1.99  --sup_passive_queue_type                priority_queues
% 11.89/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.89/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.89/1.99  --demod_completeness_check              fast
% 11.89/1.99  --demod_use_ground                      true
% 11.89/1.99  --sup_to_prop_solver                    passive
% 11.89/1.99  --sup_prop_simpl_new                    true
% 11.89/1.99  --sup_prop_simpl_given                  true
% 11.89/1.99  --sup_fun_splitting                     true
% 11.89/1.99  --sup_smt_interval                      50000
% 11.89/1.99  
% 11.89/1.99  ------ Superposition Simplification Setup
% 11.89/1.99  
% 11.89/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.89/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.89/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.89/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.89/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.89/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.89/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.89/1.99  --sup_immed_triv                        [TrivRules]
% 11.89/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/1.99  --sup_immed_bw_main                     []
% 11.89/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.89/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.89/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/1.99  --sup_input_bw                          []
% 11.89/1.99  
% 11.89/1.99  ------ Combination Options
% 11.89/1.99  
% 11.89/1.99  --comb_res_mult                         3
% 11.89/1.99  --comb_sup_mult                         2
% 11.89/1.99  --comb_inst_mult                        10
% 11.89/1.99  
% 11.89/1.99  ------ Debug Options
% 11.89/1.99  
% 11.89/1.99  --dbg_backtrace                         false
% 11.89/1.99  --dbg_dump_prop_clauses                 false
% 11.89/1.99  --dbg_dump_prop_clauses_file            -
% 11.89/1.99  --dbg_out_stat                          false
% 11.89/1.99  ------ Parsing...
% 11.89/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.89/1.99  
% 11.89/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.89/1.99  
% 11.89/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.89/1.99  
% 11.89/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.89/1.99  ------ Proving...
% 11.89/1.99  ------ Problem Properties 
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  clauses                                 24
% 11.89/1.99  conjectures                             2
% 11.89/1.99  EPR                                     3
% 11.89/1.99  Horn                                    22
% 11.89/1.99  unary                                   6
% 11.89/1.99  binary                                  14
% 11.89/1.99  lits                                    46
% 11.89/1.99  lits eq                                 13
% 11.89/1.99  fd_pure                                 0
% 11.89/1.99  fd_pseudo                               0
% 11.89/1.99  fd_cond                                 0
% 11.89/1.99  fd_pseudo_cond                          3
% 11.89/1.99  AC symbols                              0
% 11.89/1.99  
% 11.89/1.99  ------ Schedule dynamic 5 is on 
% 11.89/1.99  
% 11.89/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  ------ 
% 11.89/1.99  Current options:
% 11.89/1.99  ------ 
% 11.89/1.99  
% 11.89/1.99  ------ Input Options
% 11.89/1.99  
% 11.89/1.99  --out_options                           all
% 11.89/1.99  --tptp_safe_out                         true
% 11.89/1.99  --problem_path                          ""
% 11.89/1.99  --include_path                          ""
% 11.89/1.99  --clausifier                            res/vclausify_rel
% 11.89/1.99  --clausifier_options                    ""
% 11.89/1.99  --stdin                                 false
% 11.89/1.99  --stats_out                             all
% 11.89/1.99  
% 11.89/1.99  ------ General Options
% 11.89/1.99  
% 11.89/1.99  --fof                                   false
% 11.89/1.99  --time_out_real                         305.
% 11.89/1.99  --time_out_virtual                      -1.
% 11.89/1.99  --symbol_type_check                     false
% 11.89/1.99  --clausify_out                          false
% 11.89/1.99  --sig_cnt_out                           false
% 11.89/1.99  --trig_cnt_out                          false
% 11.89/1.99  --trig_cnt_out_tolerance                1.
% 11.89/1.99  --trig_cnt_out_sk_spl                   false
% 11.89/1.99  --abstr_cl_out                          false
% 11.89/1.99  
% 11.89/1.99  ------ Global Options
% 11.89/1.99  
% 11.89/1.99  --schedule                              default
% 11.89/1.99  --add_important_lit                     false
% 11.89/1.99  --prop_solver_per_cl                    1000
% 11.89/1.99  --min_unsat_core                        false
% 11.89/1.99  --soft_assumptions                      false
% 11.89/1.99  --soft_lemma_size                       3
% 11.89/1.99  --prop_impl_unit_size                   0
% 11.89/1.99  --prop_impl_unit                        []
% 11.89/1.99  --share_sel_clauses                     true
% 11.89/1.99  --reset_solvers                         false
% 11.89/1.99  --bc_imp_inh                            [conj_cone]
% 11.89/1.99  --conj_cone_tolerance                   3.
% 11.89/1.99  --extra_neg_conj                        none
% 11.89/1.99  --large_theory_mode                     true
% 11.89/1.99  --prolific_symb_bound                   200
% 11.89/1.99  --lt_threshold                          2000
% 11.89/1.99  --clause_weak_htbl                      true
% 11.89/1.99  --gc_record_bc_elim                     false
% 11.89/1.99  
% 11.89/1.99  ------ Preprocessing Options
% 11.89/1.99  
% 11.89/1.99  --preprocessing_flag                    true
% 11.89/1.99  --time_out_prep_mult                    0.1
% 11.89/1.99  --splitting_mode                        input
% 11.89/1.99  --splitting_grd                         true
% 11.89/1.99  --splitting_cvd                         false
% 11.89/1.99  --splitting_cvd_svl                     false
% 11.89/1.99  --splitting_nvd                         32
% 11.89/1.99  --sub_typing                            true
% 11.89/1.99  --prep_gs_sim                           true
% 11.89/1.99  --prep_unflatten                        true
% 11.89/1.99  --prep_res_sim                          true
% 11.89/1.99  --prep_upred                            true
% 11.89/1.99  --prep_sem_filter                       exhaustive
% 11.89/1.99  --prep_sem_filter_out                   false
% 11.89/1.99  --pred_elim                             true
% 11.89/1.99  --res_sim_input                         true
% 11.89/1.99  --eq_ax_congr_red                       true
% 11.89/1.99  --pure_diseq_elim                       true
% 11.89/1.99  --brand_transform                       false
% 11.89/1.99  --non_eq_to_eq                          false
% 11.89/1.99  --prep_def_merge                        true
% 11.89/1.99  --prep_def_merge_prop_impl              false
% 11.89/1.99  --prep_def_merge_mbd                    true
% 11.89/1.99  --prep_def_merge_tr_red                 false
% 11.89/1.99  --prep_def_merge_tr_cl                  false
% 11.89/1.99  --smt_preprocessing                     true
% 11.89/1.99  --smt_ac_axioms                         fast
% 11.89/1.99  --preprocessed_out                      false
% 11.89/1.99  --preprocessed_stats                    false
% 11.89/1.99  
% 11.89/1.99  ------ Abstraction refinement Options
% 11.89/1.99  
% 11.89/1.99  --abstr_ref                             []
% 11.89/1.99  --abstr_ref_prep                        false
% 11.89/1.99  --abstr_ref_until_sat                   false
% 11.89/1.99  --abstr_ref_sig_restrict                funpre
% 11.89/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.89/1.99  --abstr_ref_under                       []
% 11.89/1.99  
% 11.89/1.99  ------ SAT Options
% 11.89/1.99  
% 11.89/1.99  --sat_mode                              false
% 11.89/1.99  --sat_fm_restart_options                ""
% 11.89/1.99  --sat_gr_def                            false
% 11.89/1.99  --sat_epr_types                         true
% 11.89/1.99  --sat_non_cyclic_types                  false
% 11.89/1.99  --sat_finite_models                     false
% 11.89/1.99  --sat_fm_lemmas                         false
% 11.89/1.99  --sat_fm_prep                           false
% 11.89/1.99  --sat_fm_uc_incr                        true
% 11.89/1.99  --sat_out_model                         small
% 11.89/1.99  --sat_out_clauses                       false
% 11.89/1.99  
% 11.89/1.99  ------ QBF Options
% 11.89/1.99  
% 11.89/1.99  --qbf_mode                              false
% 11.89/1.99  --qbf_elim_univ                         false
% 11.89/1.99  --qbf_dom_inst                          none
% 11.89/1.99  --qbf_dom_pre_inst                      false
% 11.89/1.99  --qbf_sk_in                             false
% 11.89/1.99  --qbf_pred_elim                         true
% 11.89/1.99  --qbf_split                             512
% 11.89/1.99  
% 11.89/1.99  ------ BMC1 Options
% 11.89/1.99  
% 11.89/1.99  --bmc1_incremental                      false
% 11.89/1.99  --bmc1_axioms                           reachable_all
% 11.89/1.99  --bmc1_min_bound                        0
% 11.89/1.99  --bmc1_max_bound                        -1
% 11.89/1.99  --bmc1_max_bound_default                -1
% 11.89/1.99  --bmc1_symbol_reachability              true
% 11.89/1.99  --bmc1_property_lemmas                  false
% 11.89/1.99  --bmc1_k_induction                      false
% 11.89/1.99  --bmc1_non_equiv_states                 false
% 11.89/1.99  --bmc1_deadlock                         false
% 11.89/1.99  --bmc1_ucm                              false
% 11.89/1.99  --bmc1_add_unsat_core                   none
% 11.89/1.99  --bmc1_unsat_core_children              false
% 11.89/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.89/1.99  --bmc1_out_stat                         full
% 11.89/1.99  --bmc1_ground_init                      false
% 11.89/1.99  --bmc1_pre_inst_next_state              false
% 11.89/1.99  --bmc1_pre_inst_state                   false
% 11.89/1.99  --bmc1_pre_inst_reach_state             false
% 11.89/1.99  --bmc1_out_unsat_core                   false
% 11.89/1.99  --bmc1_aig_witness_out                  false
% 11.89/1.99  --bmc1_verbose                          false
% 11.89/1.99  --bmc1_dump_clauses_tptp                false
% 11.89/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.89/1.99  --bmc1_dump_file                        -
% 11.89/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.89/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.89/1.99  --bmc1_ucm_extend_mode                  1
% 11.89/1.99  --bmc1_ucm_init_mode                    2
% 11.89/1.99  --bmc1_ucm_cone_mode                    none
% 11.89/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.89/1.99  --bmc1_ucm_relax_model                  4
% 11.89/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.89/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.89/1.99  --bmc1_ucm_layered_model                none
% 11.89/1.99  --bmc1_ucm_max_lemma_size               10
% 11.89/1.99  
% 11.89/1.99  ------ AIG Options
% 11.89/1.99  
% 11.89/1.99  --aig_mode                              false
% 11.89/1.99  
% 11.89/1.99  ------ Instantiation Options
% 11.89/1.99  
% 11.89/1.99  --instantiation_flag                    true
% 11.89/1.99  --inst_sos_flag                         true
% 11.89/1.99  --inst_sos_phase                        true
% 11.89/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.89/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.89/1.99  --inst_lit_sel_side                     none
% 11.89/1.99  --inst_solver_per_active                1400
% 11.89/1.99  --inst_solver_calls_frac                1.
% 11.89/1.99  --inst_passive_queue_type               priority_queues
% 11.89/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.89/1.99  --inst_passive_queues_freq              [25;2]
% 11.89/1.99  --inst_dismatching                      true
% 11.89/1.99  --inst_eager_unprocessed_to_passive     true
% 11.89/1.99  --inst_prop_sim_given                   true
% 11.89/1.99  --inst_prop_sim_new                     false
% 11.89/1.99  --inst_subs_new                         false
% 11.89/1.99  --inst_eq_res_simp                      false
% 11.89/1.99  --inst_subs_given                       false
% 11.89/1.99  --inst_orphan_elimination               true
% 11.89/1.99  --inst_learning_loop_flag               true
% 11.89/1.99  --inst_learning_start                   3000
% 11.89/1.99  --inst_learning_factor                  2
% 11.89/1.99  --inst_start_prop_sim_after_learn       3
% 11.89/1.99  --inst_sel_renew                        solver
% 11.89/1.99  --inst_lit_activity_flag                true
% 11.89/1.99  --inst_restr_to_given                   false
% 11.89/1.99  --inst_activity_threshold               500
% 11.89/1.99  --inst_out_proof                        true
% 11.89/1.99  
% 11.89/1.99  ------ Resolution Options
% 11.89/1.99  
% 11.89/1.99  --resolution_flag                       false
% 11.89/1.99  --res_lit_sel                           adaptive
% 11.89/1.99  --res_lit_sel_side                      none
% 11.89/1.99  --res_ordering                          kbo
% 11.89/1.99  --res_to_prop_solver                    active
% 11.89/1.99  --res_prop_simpl_new                    false
% 11.89/1.99  --res_prop_simpl_given                  true
% 11.89/1.99  --res_passive_queue_type                priority_queues
% 11.89/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.89/1.99  --res_passive_queues_freq               [15;5]
% 11.89/1.99  --res_forward_subs                      full
% 11.89/1.99  --res_backward_subs                     full
% 11.89/1.99  --res_forward_subs_resolution           true
% 11.89/1.99  --res_backward_subs_resolution          true
% 11.89/1.99  --res_orphan_elimination                true
% 11.89/1.99  --res_time_limit                        2.
% 11.89/1.99  --res_out_proof                         true
% 11.89/1.99  
% 11.89/1.99  ------ Superposition Options
% 11.89/1.99  
% 11.89/1.99  --superposition_flag                    true
% 11.89/1.99  --sup_passive_queue_type                priority_queues
% 11.89/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.89/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.89/1.99  --demod_completeness_check              fast
% 11.89/1.99  --demod_use_ground                      true
% 11.89/1.99  --sup_to_prop_solver                    passive
% 11.89/1.99  --sup_prop_simpl_new                    true
% 11.89/1.99  --sup_prop_simpl_given                  true
% 11.89/1.99  --sup_fun_splitting                     true
% 11.89/1.99  --sup_smt_interval                      50000
% 11.89/1.99  
% 11.89/1.99  ------ Superposition Simplification Setup
% 11.89/1.99  
% 11.89/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.89/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.89/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.89/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.89/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.89/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.89/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.89/1.99  --sup_immed_triv                        [TrivRules]
% 11.89/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/1.99  --sup_immed_bw_main                     []
% 11.89/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.89/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.89/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/1.99  --sup_input_bw                          []
% 11.89/1.99  
% 11.89/1.99  ------ Combination Options
% 11.89/1.99  
% 11.89/1.99  --comb_res_mult                         3
% 11.89/1.99  --comb_sup_mult                         2
% 11.89/1.99  --comb_inst_mult                        10
% 11.89/1.99  
% 11.89/1.99  ------ Debug Options
% 11.89/1.99  
% 11.89/1.99  --dbg_backtrace                         false
% 11.89/1.99  --dbg_dump_prop_clauses                 false
% 11.89/1.99  --dbg_dump_prop_clauses_file            -
% 11.89/1.99  --dbg_out_stat                          false
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  ------ Proving...
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  % SZS status Theorem for theBenchmark.p
% 11.89/1.99  
% 11.89/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.89/1.99  
% 11.89/1.99  fof(f14,axiom,(
% 11.89/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f27,plain,(
% 11.89/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.89/1.99    inference(ennf_transformation,[],[f14])).
% 11.89/1.99  
% 11.89/1.99  fof(f36,plain,(
% 11.89/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.89/1.99    inference(nnf_transformation,[],[f27])).
% 11.89/1.99  
% 11.89/1.99  fof(f61,plain,(
% 11.89/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.89/1.99    inference(cnf_transformation,[],[f36])).
% 11.89/1.99  
% 11.89/1.99  fof(f17,conjecture,(
% 11.89/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f18,negated_conjecture,(
% 11.89/1.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.89/1.99    inference(negated_conjecture,[],[f17])).
% 11.89/1.99  
% 11.89/1.99  fof(f29,plain,(
% 11.89/1.99    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.89/1.99    inference(ennf_transformation,[],[f18])).
% 11.89/1.99  
% 11.89/1.99  fof(f37,plain,(
% 11.89/1.99    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.89/1.99    inference(nnf_transformation,[],[f29])).
% 11.89/1.99  
% 11.89/1.99  fof(f38,plain,(
% 11.89/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.89/1.99    inference(flattening,[],[f37])).
% 11.89/1.99  
% 11.89/1.99  fof(f40,plain,(
% 11.89/1.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 11.89/1.99    introduced(choice_axiom,[])).
% 11.89/1.99  
% 11.89/1.99  fof(f39,plain,(
% 11.89/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 11.89/1.99    introduced(choice_axiom,[])).
% 11.89/1.99  
% 11.89/1.99  fof(f41,plain,(
% 11.89/1.99    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.89/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f40,f39])).
% 11.89/1.99  
% 11.89/1.99  fof(f68,plain,(
% 11.89/1.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 11.89/1.99    inference(cnf_transformation,[],[f41])).
% 11.89/1.99  
% 11.89/1.99  fof(f16,axiom,(
% 11.89/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f66,plain,(
% 11.89/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.89/1.99    inference(cnf_transformation,[],[f16])).
% 11.89/1.99  
% 11.89/1.99  fof(f13,axiom,(
% 11.89/1.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f32,plain,(
% 11.89/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.89/1.99    inference(nnf_transformation,[],[f13])).
% 11.89/1.99  
% 11.89/1.99  fof(f33,plain,(
% 11.89/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.89/1.99    inference(rectify,[],[f32])).
% 11.89/1.99  
% 11.89/1.99  fof(f34,plain,(
% 11.89/1.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.89/1.99    introduced(choice_axiom,[])).
% 11.89/1.99  
% 11.89/1.99  fof(f35,plain,(
% 11.89/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.89/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 11.89/1.99  
% 11.89/1.99  fof(f57,plain,(
% 11.89/1.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.89/1.99    inference(cnf_transformation,[],[f35])).
% 11.89/1.99  
% 11.89/1.99  fof(f79,plain,(
% 11.89/1.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.89/1.99    inference(equality_resolution,[],[f57])).
% 11.89/1.99  
% 11.89/1.99  fof(f9,axiom,(
% 11.89/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f23,plain,(
% 11.89/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.89/1.99    inference(ennf_transformation,[],[f9])).
% 11.89/1.99  
% 11.89/1.99  fof(f53,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.89/1.99    inference(cnf_transformation,[],[f23])).
% 11.89/1.99  
% 11.89/1.99  fof(f2,axiom,(
% 11.89/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f43,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.89/1.99    inference(cnf_transformation,[],[f2])).
% 11.89/1.99  
% 11.89/1.99  fof(f15,axiom,(
% 11.89/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f28,plain,(
% 11.89/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.89/1.99    inference(ennf_transformation,[],[f15])).
% 11.89/1.99  
% 11.89/1.99  fof(f65,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.89/1.99    inference(cnf_transformation,[],[f28])).
% 11.89/1.99  
% 11.89/1.99  fof(f5,axiom,(
% 11.89/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f48,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.89/1.99    inference(cnf_transformation,[],[f5])).
% 11.89/1.99  
% 11.89/1.99  fof(f75,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.89/1.99    inference(definition_unfolding,[],[f65,f48])).
% 11.89/1.99  
% 11.89/1.99  fof(f69,plain,(
% 11.89/1.99    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 11.89/1.99    inference(cnf_transformation,[],[f41])).
% 11.89/1.99  
% 11.89/1.99  fof(f67,plain,(
% 11.89/1.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.89/1.99    inference(cnf_transformation,[],[f41])).
% 11.89/1.99  
% 11.89/1.99  fof(f6,axiom,(
% 11.89/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f20,plain,(
% 11.89/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.89/1.99    inference(ennf_transformation,[],[f6])).
% 11.89/1.99  
% 11.89/1.99  fof(f50,plain,(
% 11.89/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.89/1.99    inference(cnf_transformation,[],[f20])).
% 11.89/1.99  
% 11.89/1.99  fof(f71,plain,(
% 11.89/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 11.89/1.99    inference(definition_unfolding,[],[f50,f48])).
% 11.89/1.99  
% 11.89/1.99  fof(f3,axiom,(
% 11.89/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f19,plain,(
% 11.89/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.89/1.99    inference(ennf_transformation,[],[f3])).
% 11.89/1.99  
% 11.89/1.99  fof(f44,plain,(
% 11.89/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.89/1.99    inference(cnf_transformation,[],[f19])).
% 11.89/1.99  
% 11.89/1.99  fof(f70,plain,(
% 11.89/1.99    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 11.89/1.99    inference(cnf_transformation,[],[f41])).
% 11.89/1.99  
% 11.89/1.99  fof(f10,axiom,(
% 11.89/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f24,plain,(
% 11.89/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 11.89/1.99    inference(ennf_transformation,[],[f10])).
% 11.89/1.99  
% 11.89/1.99  fof(f54,plain,(
% 11.89/1.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 11.89/1.99    inference(cnf_transformation,[],[f24])).
% 11.89/1.99  
% 11.89/1.99  fof(f73,plain,(
% 11.89/1.99    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) | ~r1_tarski(X0,X1)) )),
% 11.89/1.99    inference(definition_unfolding,[],[f54,f48,f48])).
% 11.89/1.99  
% 11.89/1.99  fof(f11,axiom,(
% 11.89/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f55,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.89/1.99    inference(cnf_transformation,[],[f11])).
% 11.89/1.99  
% 11.89/1.99  fof(f74,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 11.89/1.99    inference(definition_unfolding,[],[f55,f48])).
% 11.89/1.99  
% 11.89/1.99  fof(f12,axiom,(
% 11.89/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f25,plain,(
% 11.89/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 11.89/1.99    inference(ennf_transformation,[],[f12])).
% 11.89/1.99  
% 11.89/1.99  fof(f26,plain,(
% 11.89/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.89/1.99    inference(flattening,[],[f25])).
% 11.89/1.99  
% 11.89/1.99  fof(f56,plain,(
% 11.89/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.89/1.99    inference(cnf_transformation,[],[f26])).
% 11.89/1.99  
% 11.89/1.99  fof(f8,axiom,(
% 11.89/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f22,plain,(
% 11.89/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.89/1.99    inference(ennf_transformation,[],[f8])).
% 11.89/1.99  
% 11.89/1.99  fof(f52,plain,(
% 11.89/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.89/1.99    inference(cnf_transformation,[],[f22])).
% 11.89/1.99  
% 11.89/1.99  fof(f4,axiom,(
% 11.89/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.89/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.89/1.99  
% 11.89/1.99  fof(f30,plain,(
% 11.89/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.89/1.99    inference(nnf_transformation,[],[f4])).
% 11.89/1.99  
% 11.89/1.99  fof(f31,plain,(
% 11.89/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.89/1.99    inference(flattening,[],[f30])).
% 11.89/1.99  
% 11.89/1.99  fof(f47,plain,(
% 11.89/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.89/1.99    inference(cnf_transformation,[],[f31])).
% 11.89/1.99  
% 11.89/1.99  fof(f45,plain,(
% 11.89/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.89/1.99    inference(cnf_transformation,[],[f31])).
% 11.89/1.99  
% 11.89/1.99  fof(f77,plain,(
% 11.89/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.89/1.99    inference(equality_resolution,[],[f45])).
% 11.89/1.99  
% 11.89/1.99  cnf(c_21,plain,
% 11.89/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.89/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_26,negated_conjecture,
% 11.89/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 11.89/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_482,plain,
% 11.89/1.99      ( r2_hidden(X0,X1)
% 11.89/1.99      | v1_xboole_0(X1)
% 11.89/1.99      | k1_zfmisc_1(sK1) != X1
% 11.89/1.99      | sK3 != X0 ),
% 11.89/1.99      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_483,plain,
% 11.89/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.89/1.99      inference(unflattening,[status(thm)],[c_482]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_23,plain,
% 11.89/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.89/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_33,plain,
% 11.89/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.89/1.99      inference(instantiation,[status(thm)],[c_23]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_485,plain,
% 11.89/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 11.89/1.99      inference(global_propositional_subsumption,
% 11.89/1.99                [status(thm)],
% 11.89/1.99                [c_483,c_33]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1391,plain,
% 11.89/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_17,plain,
% 11.89/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.89/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1394,plain,
% 11.89/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.89/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_2847,plain,
% 11.89/1.99      ( r1_tarski(sK3,sK1) = iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_1391,c_1394]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_10,plain,
% 11.89/1.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.89/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1400,plain,
% 11.89/1.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_3164,plain,
% 11.89/1.99      ( k3_xboole_0(sK3,sK1) = sK3 ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_2847,c_1400]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1,plain,
% 11.89/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.89/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_4539,plain,
% 11.89/1.99      ( k3_xboole_0(sK1,sK3) = sK3 ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_3164,c_1]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_22,plain,
% 11.89/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.89/1.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 11.89/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_518,plain,
% 11.89/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 11.89/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.89/1.99      | sK3 != X1 ),
% 11.89/1.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_519,plain,
% 11.89/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
% 11.89/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.89/1.99      inference(unflattening,[status(thm)],[c_518]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1519,plain,
% 11.89/1.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 11.89/1.99      inference(equality_resolution,[status(thm)],[c_519]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_4780,plain,
% 11.89/1.99      ( k3_subset_1(sK1,sK3) = k5_xboole_0(sK1,sK3) ),
% 11.89/1.99      inference(demodulation,[status(thm)],[c_4539,c_1519]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_25,negated_conjecture,
% 11.89/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.89/1.99      | r1_tarski(sK2,sK3) ),
% 11.89/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1392,plain,
% 11.89/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 11.89/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_4996,plain,
% 11.89/1.99      ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 11.89/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.89/1.99      inference(demodulation,[status(thm)],[c_4780,c_1392]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_27,negated_conjecture,
% 11.89/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.89/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_527,plain,
% 11.89/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 11.89/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.89/1.99      | sK2 != X1 ),
% 11.89/1.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_528,plain,
% 11.89/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
% 11.89/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.89/1.99      inference(unflattening,[status(thm)],[c_527]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1520,plain,
% 11.89/1.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 11.89/1.99      inference(equality_resolution,[status(thm)],[c_528]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_6,plain,
% 11.89/1.99      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 11.89/1.99      | r1_xboole_0(X0,X2) ),
% 11.89/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1404,plain,
% 11.89/1.99      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 11.89/1.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_4788,plain,
% 11.89/1.99      ( r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
% 11.89/1.99      | r1_xboole_0(X0,sK2) = iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_1520,c_1404]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_5241,plain,
% 11.89/1.99      ( r1_tarski(sK2,sK3) = iProver_top
% 11.89/1.99      | r1_xboole_0(k5_xboole_0(sK1,sK3),sK2) = iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_4996,c_4788]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_2,plain,
% 11.89/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.89/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1407,plain,
% 11.89/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 11.89/1.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_5351,plain,
% 11.89/1.99      ( r1_tarski(sK2,sK3) = iProver_top
% 11.89/1.99      | r1_xboole_0(sK2,k5_xboole_0(sK1,sK3)) = iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_5241,c_1407]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_500,plain,
% 11.89/1.99      ( r2_hidden(X0,X1)
% 11.89/1.99      | v1_xboole_0(X1)
% 11.89/1.99      | k1_zfmisc_1(sK1) != X1
% 11.89/1.99      | sK2 != X0 ),
% 11.89/1.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_501,plain,
% 11.89/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.89/1.99      inference(unflattening,[status(thm)],[c_500]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_503,plain,
% 11.89/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 11.89/1.99      inference(global_propositional_subsumption,
% 11.89/1.99                [status(thm)],
% 11.89/1.99                [c_501,c_33]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1390,plain,
% 11.89/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_2848,plain,
% 11.89/1.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_1390,c_1394]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_3341,plain,
% 11.89/1.99      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_2848,c_1400]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_7155,plain,
% 11.89/1.99      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_3341,c_1]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_7602,plain,
% 11.89/1.99      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 11.89/1.99      inference(demodulation,[status(thm)],[c_7155,c_1520]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_24,negated_conjecture,
% 11.89/1.99      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.89/1.99      | ~ r1_tarski(sK2,sK3) ),
% 11.89/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1393,plain,
% 11.89/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 11.89/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_4997,plain,
% 11.89/1.99      ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 11.89/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.89/1.99      inference(demodulation,[status(thm)],[c_4780,c_1393]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_7807,plain,
% 11.89/1.99      ( r1_tarski(k5_xboole_0(sK1,sK3),k5_xboole_0(sK1,sK2)) != iProver_top
% 11.89/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.89/1.99      inference(demodulation,[status(thm)],[c_7602,c_4997]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_11,plain,
% 11.89/1.99      ( ~ r1_tarski(X0,X1)
% 11.89/1.99      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
% 11.89/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1399,plain,
% 11.89/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.89/1.99      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_6178,plain,
% 11.89/1.99      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_subset_1(sK1,sK2)) = iProver_top
% 11.89/1.99      | r1_tarski(sK2,X0) != iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_1520,c_1399]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_6527,plain,
% 11.89/1.99      ( r1_tarski(k5_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 11.89/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_4539,c_6178]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_8027,plain,
% 11.89/1.99      ( r1_tarski(sK2,sK3) != iProver_top ),
% 11.89/1.99      inference(global_propositional_subsumption,
% 11.89/1.99                [status(thm)],
% 11.89/1.99                [c_7807,c_4997,c_6527]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_11749,plain,
% 11.89/1.99      ( r1_xboole_0(sK2,k5_xboole_0(sK1,sK3)) = iProver_top ),
% 11.89/1.99      inference(global_propositional_subsumption,
% 11.89/1.99                [status(thm)],
% 11.89/1.99                [c_5351,c_4997,c_6527]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_12,plain,
% 11.89/1.99      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 11.89/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_13,plain,
% 11.89/1.99      ( r1_tarski(X0,X1)
% 11.89/1.99      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.89/1.99      | ~ r1_xboole_0(X0,X2) ),
% 11.89/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1398,plain,
% 11.89/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.89/1.99      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.89/1.99      | r1_xboole_0(X0,X2) != iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_7381,plain,
% 11.89/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.89/1.99      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.89/1.99      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_12,c_1398]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_11981,plain,
% 11.89/1.99      ( r1_tarski(X0,k2_xboole_0(sK3,sK1)) != iProver_top
% 11.89/1.99      | r1_tarski(X0,sK3) = iProver_top
% 11.89/1.99      | r1_xboole_0(X0,k5_xboole_0(sK1,sK3)) != iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_4539,c_7381]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_9,plain,
% 11.89/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.89/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_1401,plain,
% 11.89/1.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_3163,plain,
% 11.89/1.99      ( k2_xboole_0(sK3,sK1) = sK1 ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_2847,c_1401]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_11989,plain,
% 11.89/1.99      ( r1_tarski(X0,sK3) = iProver_top
% 11.89/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.89/1.99      | r1_xboole_0(X0,k5_xboole_0(sK1,sK3)) != iProver_top ),
% 11.89/1.99      inference(light_normalisation,[status(thm)],[c_11981,c_3163]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_46217,plain,
% 11.89/1.99      ( r1_tarski(sK2,sK3) = iProver_top
% 11.89/1.99      | r1_tarski(sK2,sK1) != iProver_top ),
% 11.89/1.99      inference(superposition,[status(thm)],[c_11749,c_11989]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_955,plain,
% 11.89/1.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.89/1.99      theory(equality) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_960,plain,
% 11.89/1.99      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 11.89/1.99      inference(instantiation,[status(thm)],[c_955]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_203,plain,
% 11.89/1.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.89/1.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_204,plain,
% 11.89/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.89/1.99      inference(renaming,[status(thm)],[c_203]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_641,plain,
% 11.89/1.99      ( r1_tarski(X0,X1)
% 11.89/1.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 11.89/1.99      | sK2 != X0 ),
% 11.89/1.99      inference(resolution_lifted,[status(thm)],[c_204,c_503]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_642,plain,
% 11.89/1.99      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.89/1.99      inference(unflattening,[status(thm)],[c_641]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_643,plain,
% 11.89/1.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.89/1.99      | r1_tarski(sK2,X0) = iProver_top ),
% 11.89/1.99      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_645,plain,
% 11.89/1.99      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 11.89/1.99      | r1_tarski(sK2,sK1) = iProver_top ),
% 11.89/1.99      inference(instantiation,[status(thm)],[c_643]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_3,plain,
% 11.89/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.89/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_87,plain,
% 11.89/1.99      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 11.89/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_5,plain,
% 11.89/1.99      ( r1_tarski(X0,X0) ),
% 11.89/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(c_83,plain,
% 11.89/1.99      ( r1_tarski(sK1,sK1) ),
% 11.89/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.89/1.99  
% 11.89/1.99  cnf(contradiction,plain,
% 11.89/1.99      ( $false ),
% 11.89/1.99      inference(minisat,
% 11.89/1.99                [status(thm)],
% 11.89/1.99                [c_46217,c_8027,c_960,c_645,c_87,c_83]) ).
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.89/1.99  
% 11.89/1.99  ------                               Statistics
% 11.89/1.99  
% 11.89/1.99  ------ General
% 11.89/1.99  
% 11.89/1.99  abstr_ref_over_cycles:                  0
% 11.89/1.99  abstr_ref_under_cycles:                 0
% 11.89/1.99  gc_basic_clause_elim:                   0
% 11.89/1.99  forced_gc_time:                         0
% 11.89/1.99  parsing_time:                           0.009
% 11.89/1.99  unif_index_cands_time:                  0.
% 11.89/1.99  unif_index_add_time:                    0.
% 11.89/1.99  orderings_time:                         0.
% 11.89/1.99  out_proof_time:                         0.01
% 11.89/1.99  total_time:                             1.464
% 11.89/1.99  num_of_symbols:                         45
% 11.89/1.99  num_of_terms:                           53611
% 11.89/1.99  
% 11.89/1.99  ------ Preprocessing
% 11.89/1.99  
% 11.89/1.99  num_of_splits:                          0
% 11.89/1.99  num_of_split_atoms:                     0
% 11.89/1.99  num_of_reused_defs:                     0
% 11.89/1.99  num_eq_ax_congr_red:                    22
% 11.89/1.99  num_of_sem_filtered_clauses:            1
% 11.89/1.99  num_of_subtypes:                        0
% 11.89/1.99  monotx_restored_types:                  0
% 11.89/1.99  sat_num_of_epr_types:                   0
% 11.89/1.99  sat_num_of_non_cyclic_types:            0
% 11.89/1.99  sat_guarded_non_collapsed_types:        0
% 11.89/1.99  num_pure_diseq_elim:                    0
% 11.89/1.99  simp_replaced_by:                       0
% 11.89/1.99  res_preprocessed:                       118
% 11.89/1.99  prep_upred:                             0
% 11.89/1.99  prep_unflattend:                        46
% 11.89/1.99  smt_new_axioms:                         0
% 11.89/1.99  pred_elim_cands:                        3
% 11.89/1.99  pred_elim:                              2
% 11.89/1.99  pred_elim_cl:                           3
% 11.89/1.99  pred_elim_cycles:                       5
% 11.89/1.99  merged_defs:                            16
% 11.89/1.99  merged_defs_ncl:                        0
% 11.89/1.99  bin_hyper_res:                          17
% 11.89/1.99  prep_cycles:                            4
% 11.89/1.99  pred_elim_time:                         0.006
% 11.89/1.99  splitting_time:                         0.
% 11.89/1.99  sem_filter_time:                        0.
% 11.89/1.99  monotx_time:                            0.
% 11.89/1.99  subtype_inf_time:                       0.
% 11.89/1.99  
% 11.89/1.99  ------ Problem properties
% 11.89/1.99  
% 11.89/1.99  clauses:                                24
% 11.89/1.99  conjectures:                            2
% 11.89/1.99  epr:                                    3
% 11.89/1.99  horn:                                   22
% 11.89/1.99  ground:                                 4
% 11.89/1.99  unary:                                  6
% 11.89/1.99  binary:                                 14
% 11.89/1.99  lits:                                   46
% 11.89/1.99  lits_eq:                                13
% 11.89/1.99  fd_pure:                                0
% 11.89/1.99  fd_pseudo:                              0
% 11.89/1.99  fd_cond:                                0
% 11.89/1.99  fd_pseudo_cond:                         3
% 11.89/1.99  ac_symbols:                             0
% 11.89/1.99  
% 11.89/1.99  ------ Propositional Solver
% 11.89/1.99  
% 11.89/1.99  prop_solver_calls:                      31
% 11.89/1.99  prop_fast_solver_calls:                 1356
% 11.89/1.99  smt_solver_calls:                       0
% 11.89/1.99  smt_fast_solver_calls:                  0
% 11.89/1.99  prop_num_of_clauses:                    21686
% 11.89/1.99  prop_preprocess_simplified:             31361
% 11.89/1.99  prop_fo_subsumed:                       47
% 11.89/1.99  prop_solver_time:                       0.
% 11.89/1.99  smt_solver_time:                        0.
% 11.89/1.99  smt_fast_solver_time:                   0.
% 11.89/1.99  prop_fast_solver_time:                  0.
% 11.89/1.99  prop_unsat_core_time:                   0.002
% 11.89/1.99  
% 11.89/1.99  ------ QBF
% 11.89/1.99  
% 11.89/1.99  qbf_q_res:                              0
% 11.89/1.99  qbf_num_tautologies:                    0
% 11.89/1.99  qbf_prep_cycles:                        0
% 11.89/1.99  
% 11.89/1.99  ------ BMC1
% 11.89/1.99  
% 11.89/1.99  bmc1_current_bound:                     -1
% 11.89/1.99  bmc1_last_solved_bound:                 -1
% 11.89/1.99  bmc1_unsat_core_size:                   -1
% 11.89/1.99  bmc1_unsat_core_parents_size:           -1
% 11.89/1.99  bmc1_merge_next_fun:                    0
% 11.89/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.89/1.99  
% 11.89/1.99  ------ Instantiation
% 11.89/1.99  
% 11.89/1.99  inst_num_of_clauses:                    4137
% 11.89/1.99  inst_num_in_passive:                    1573
% 11.89/1.99  inst_num_in_active:                     1410
% 11.89/1.99  inst_num_in_unprocessed:                1158
% 11.89/1.99  inst_num_of_loops:                      1570
% 11.89/1.99  inst_num_of_learning_restarts:          0
% 11.89/1.99  inst_num_moves_active_passive:          157
% 11.89/1.99  inst_lit_activity:                      0
% 11.89/1.99  inst_lit_activity_moves:                0
% 11.89/1.99  inst_num_tautologies:                   0
% 11.89/1.99  inst_num_prop_implied:                  0
% 11.89/1.99  inst_num_existing_simplified:           0
% 11.89/1.99  inst_num_eq_res_simplified:             0
% 11.89/1.99  inst_num_child_elim:                    0
% 11.89/1.99  inst_num_of_dismatching_blockings:      3707
% 11.89/1.99  inst_num_of_non_proper_insts:           4820
% 11.89/1.99  inst_num_of_duplicates:                 0
% 11.89/1.99  inst_inst_num_from_inst_to_res:         0
% 11.89/1.99  inst_dismatching_checking_time:         0.
% 11.89/1.99  
% 11.89/1.99  ------ Resolution
% 11.89/1.99  
% 11.89/1.99  res_num_of_clauses:                     0
% 11.89/1.99  res_num_in_passive:                     0
% 11.89/1.99  res_num_in_active:                      0
% 11.89/1.99  res_num_of_loops:                       122
% 11.89/1.99  res_forward_subset_subsumed:            252
% 11.89/1.99  res_backward_subset_subsumed:           16
% 11.89/1.99  res_forward_subsumed:                   3
% 11.89/1.99  res_backward_subsumed:                  0
% 11.89/1.99  res_forward_subsumption_resolution:     2
% 11.89/1.99  res_backward_subsumption_resolution:    0
% 11.89/1.99  res_clause_to_clause_subsumption:       21705
% 11.89/1.99  res_orphan_elimination:                 0
% 11.89/1.99  res_tautology_del:                      184
% 11.89/1.99  res_num_eq_res_simplified:              0
% 11.89/1.99  res_num_sel_changes:                    0
% 11.89/1.99  res_moves_from_active_to_pass:          0
% 11.89/1.99  
% 11.89/1.99  ------ Superposition
% 11.89/1.99  
% 11.89/1.99  sup_time_total:                         0.
% 11.89/1.99  sup_time_generating:                    0.
% 11.89/1.99  sup_time_sim_full:                      0.
% 11.89/1.99  sup_time_sim_immed:                     0.
% 11.89/1.99  
% 11.89/1.99  sup_num_of_clauses:                     2509
% 11.89/1.99  sup_num_in_active:                      274
% 11.89/1.99  sup_num_in_passive:                     2235
% 11.89/1.99  sup_num_of_loops:                       312
% 11.89/1.99  sup_fw_superposition:                   3663
% 11.89/1.99  sup_bw_superposition:                   3080
% 11.89/1.99  sup_immediate_simplified:               1691
% 11.89/1.99  sup_given_eliminated:                   0
% 11.89/1.99  comparisons_done:                       0
% 11.89/1.99  comparisons_avoided:                    41
% 11.89/1.99  
% 11.89/1.99  ------ Simplifications
% 11.89/1.99  
% 11.89/1.99  
% 11.89/1.99  sim_fw_subset_subsumed:                 45
% 11.89/1.99  sim_bw_subset_subsumed:                 72
% 11.89/1.99  sim_fw_subsumed:                        110
% 11.89/1.99  sim_bw_subsumed:                        11
% 11.89/1.99  sim_fw_subsumption_res:                 0
% 11.89/1.99  sim_bw_subsumption_res:                 0
% 11.89/1.99  sim_tautology_del:                      53
% 11.89/1.99  sim_eq_tautology_del:                   45
% 11.89/1.99  sim_eq_res_simp:                        0
% 11.89/1.99  sim_fw_demodulated:                     103
% 11.89/1.99  sim_bw_demodulated:                     32
% 11.89/1.99  sim_light_normalised:                   1581
% 11.89/1.99  sim_joinable_taut:                      0
% 11.89/1.99  sim_joinable_simp:                      0
% 11.89/1.99  sim_ac_normalised:                      0
% 11.89/1.99  sim_smt_subsumption:                    0
% 11.89/1.99  
%------------------------------------------------------------------------------
