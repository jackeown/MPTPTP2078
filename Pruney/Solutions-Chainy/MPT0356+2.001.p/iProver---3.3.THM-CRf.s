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
% DateTime   : Thu Dec  3 11:39:42 EST 2020

% Result     : Theorem 42.85s
% Output     : CNFRefutation 43.44s
% Verified   : 
% Statistics : Number of formulae       :  236 (7694 expanded)
%              Number of clauses        :  167 (2793 expanded)
%              Number of leaves         :   24 (1649 expanded)
%              Depth                    :   50
%              Number of atoms          :  510 (25280 expanded)
%              Number of equality atoms :  240 (4552 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :   27 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(sK3,k3_subset_1(X0,X1))
        & r1_tarski(X1,k3_subset_1(X0,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK1,sK2))
          & r1_tarski(sK2,k3_subset_1(sK1,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2))
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42,f41])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f57,f57])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ~ r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1632,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_626,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_627,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_1926,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_627])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1619,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2734,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1926,c_1619])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_367,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X3))
    | r1_tarski(X0,k4_xboole_0(X1,X3)) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

cnf(c_1618,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X3)) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_6574,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k4_xboole_0(X0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_1618])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1630,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7122,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(X0,sK3)) = k4_xboole_0(X0,sK3)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_1630])).

cnf(c_7268,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1632,c_7122])).

cnf(c_11,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1627,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3612,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1627,c_1630])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5246,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_3612,c_1])).

cnf(c_7274,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_7268,c_5246])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36908,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_7274,c_2])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_522,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_523,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_17,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_226,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_452,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X0 != X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_226,c_21])).

cnf(c_453,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_453,c_24])).

cnf(c_527,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_23,c_18,c_463])).

cnf(c_931,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_932,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_931])).

cnf(c_977,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_527,c_932])).

cnf(c_1614,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_7120,plain,
    ( k3_subset_1(k4_xboole_0(X0,sK3),sK2) = k4_xboole_0(k4_xboole_0(X0,sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_1614])).

cnf(c_7798,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_7120])).

cnf(c_10637,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_7798])).

cnf(c_11610,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_10637])).

cnf(c_11805,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_11610])).

cnf(c_12249,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_11805])).

cnf(c_13118,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_12249])).

cnf(c_13364,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_13118])).

cnf(c_13862,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_13364])).

cnf(c_14721,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_13862])).

cnf(c_14995,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_14721])).

cnf(c_16862,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_14995])).

cnf(c_17123,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_16862])).

cnf(c_17429,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_17123])).

cnf(c_18074,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_17429])).

cnf(c_18191,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_18074])).

cnf(c_18396,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_18191])).

cnf(c_18819,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_18396])).

cnf(c_19408,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_18819])).

cnf(c_20563,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_19408])).

cnf(c_20699,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_20563])).

cnf(c_20976,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_20699])).

cnf(c_21624,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_20976])).

cnf(c_22293,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_21624])).

cnf(c_22482,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6574,c_22293])).

cnf(c_24601,plain,
    ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) ),
    inference(superposition,[status(thm)],[c_1632,c_22482])).

cnf(c_5464,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1627,c_1614])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_635,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_636,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK2)) = sK2
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_2052,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK2)) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_636])).

cnf(c_644,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_645,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_2053,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_645])).

cnf(c_2736,plain,
    ( k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2052,c_2052,c_2053])).

cnf(c_22686,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_5464,c_2736])).

cnf(c_504,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,k3_subset_1(X3,X2)) = X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_25,c_18,c_463])).

cnf(c_976,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_509,c_932])).

cnf(c_1613,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_4041,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1627,c_1613])).

cnf(c_10793,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_4041,c_4041,c_5464])).

cnf(c_10795,plain,
    ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_10793])).

cnf(c_23769,plain,
    ( k3_subset_1(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_22686,c_10795])).

cnf(c_24610,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_24601,c_7274,c_23769])).

cnf(c_36964,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_36908,c_24610])).

cnf(c_13,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1625,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_581,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_582,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_42,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_584,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_42])).

cnf(c_1615,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_1621,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4053,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1615,c_1621])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1629,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8899,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4053,c_1629])).

cnf(c_9374,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_8899])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1626,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_39785,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9374,c_1626])).

cnf(c_61136,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_39785,c_1630])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1628,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3611,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1628,c_1630])).

cnf(c_3921,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_3611,c_1])).

cnf(c_61182,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_61136,c_3921])).

cnf(c_74130,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_36964,c_36964,c_61182])).

cnf(c_3324,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1627])).

cnf(c_6575,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X3) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X3,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3324,c_1618])).

cnf(c_74429,plain,
    ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))),X0) != iProver_top
    | r1_tarski(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_74130,c_6575])).

cnf(c_6779,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_1626])).

cnf(c_39300,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_6779,c_1630])).

cnf(c_58161,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39300,c_3921])).

cnf(c_617,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_618,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK3)) = sK3
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_1925,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK3)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_618])).

cnf(c_2634,plain,
    ( k3_subset_1(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1925,c_1925,c_1926])).

cnf(c_22685,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_5464,c_2634])).

cnf(c_23438,plain,
    ( k3_subset_1(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_22685,c_10795])).

cnf(c_5462,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1632,c_1614])).

cnf(c_23485,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_23438,c_5462])).

cnf(c_23448,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_22685,c_2])).

cnf(c_23491,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_23485,c_23448])).

cnf(c_58175,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_58161,c_23491])).

cnf(c_5643,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_5246])).

cnf(c_74293,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_74130,c_5643])).

cnf(c_74704,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK2),sK3) = k4_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_74293,c_58175])).

cnf(c_74705,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_74704,c_3612])).

cnf(c_74804,plain,
    ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)),X0) != iProver_top
    | r1_tarski(sK3,k4_xboole_0(X0,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_74429,c_58175,c_74705])).

cnf(c_4039,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1632,c_1613])).

cnf(c_6313,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4039,c_4039,c_5462])).

cnf(c_22690,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_5464,c_6313])).

cnf(c_74805,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k4_xboole_0(X0,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_74804,c_22690])).

cnf(c_75117,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK3,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74805])).

cnf(c_1163,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1672,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_1750,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_2301,plain,
    ( r1_tarski(sK3,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK3,k4_xboole_0(sK1,sK2))
    | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_2302,plain,
    ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | sK3 != sK3
    | r1_tarski(sK3,k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK3,k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2301])).

cnf(c_1159,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1891,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_1164,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1170,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_223,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_563,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_564,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_566,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_42])).

cnf(c_802,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_566])).

cnf(c_803,plain,
    ( r1_tarski(sK3,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_804,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_806,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r1_tarski(sK3,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_646,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_99,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_95,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( r1_tarski(sK3,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75117,c_2302,c_1891,c_1170,c_806,c_646,c_99,c_95,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:15:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 42.85/5.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.85/5.99  
% 42.85/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 42.85/5.99  
% 42.85/5.99  ------  iProver source info
% 42.85/5.99  
% 42.85/5.99  git: date: 2020-06-30 10:37:57 +0100
% 42.85/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 42.85/5.99  git: non_committed_changes: false
% 42.85/5.99  git: last_make_outside_of_git: false
% 42.85/5.99  
% 42.85/5.99  ------ 
% 42.85/5.99  
% 42.85/5.99  ------ Input Options
% 42.85/5.99  
% 42.85/5.99  --out_options                           all
% 42.85/5.99  --tptp_safe_out                         true
% 42.85/5.99  --problem_path                          ""
% 42.85/5.99  --include_path                          ""
% 42.85/5.99  --clausifier                            res/vclausify_rel
% 42.85/5.99  --clausifier_options                    ""
% 42.85/5.99  --stdin                                 false
% 42.85/5.99  --stats_out                             all
% 42.85/5.99  
% 42.85/5.99  ------ General Options
% 42.85/5.99  
% 42.85/5.99  --fof                                   false
% 42.85/5.99  --time_out_real                         305.
% 42.85/5.99  --time_out_virtual                      -1.
% 42.85/5.99  --symbol_type_check                     false
% 42.85/5.99  --clausify_out                          false
% 42.85/5.99  --sig_cnt_out                           false
% 42.85/5.99  --trig_cnt_out                          false
% 42.85/5.99  --trig_cnt_out_tolerance                1.
% 42.85/5.99  --trig_cnt_out_sk_spl                   false
% 42.85/5.99  --abstr_cl_out                          false
% 42.85/5.99  
% 42.85/5.99  ------ Global Options
% 42.85/5.99  
% 42.85/5.99  --schedule                              default
% 42.85/5.99  --add_important_lit                     false
% 42.85/5.99  --prop_solver_per_cl                    1000
% 42.85/5.99  --min_unsat_core                        false
% 42.85/5.99  --soft_assumptions                      false
% 42.85/5.99  --soft_lemma_size                       3
% 42.85/5.99  --prop_impl_unit_size                   0
% 42.85/5.99  --prop_impl_unit                        []
% 42.85/5.99  --share_sel_clauses                     true
% 42.85/5.99  --reset_solvers                         false
% 42.85/5.99  --bc_imp_inh                            [conj_cone]
% 42.85/5.99  --conj_cone_tolerance                   3.
% 42.85/5.99  --extra_neg_conj                        none
% 42.85/5.99  --large_theory_mode                     true
% 42.85/5.99  --prolific_symb_bound                   200
% 42.85/5.99  --lt_threshold                          2000
% 42.85/5.99  --clause_weak_htbl                      true
% 42.85/5.99  --gc_record_bc_elim                     false
% 42.85/5.99  
% 42.85/5.99  ------ Preprocessing Options
% 42.85/5.99  
% 42.85/5.99  --preprocessing_flag                    true
% 42.85/5.99  --time_out_prep_mult                    0.1
% 42.85/5.99  --splitting_mode                        input
% 42.85/5.99  --splitting_grd                         true
% 42.85/5.99  --splitting_cvd                         false
% 42.85/5.99  --splitting_cvd_svl                     false
% 42.85/5.99  --splitting_nvd                         32
% 42.85/5.99  --sub_typing                            true
% 42.85/5.99  --prep_gs_sim                           true
% 42.85/5.99  --prep_unflatten                        true
% 42.85/5.99  --prep_res_sim                          true
% 42.85/5.99  --prep_upred                            true
% 42.85/5.99  --prep_sem_filter                       exhaustive
% 42.85/5.99  --prep_sem_filter_out                   false
% 42.85/5.99  --pred_elim                             true
% 42.85/5.99  --res_sim_input                         true
% 42.85/5.99  --eq_ax_congr_red                       true
% 42.85/5.99  --pure_diseq_elim                       true
% 42.85/5.99  --brand_transform                       false
% 42.85/5.99  --non_eq_to_eq                          false
% 42.85/5.99  --prep_def_merge                        true
% 42.85/5.99  --prep_def_merge_prop_impl              false
% 42.85/5.99  --prep_def_merge_mbd                    true
% 42.85/5.99  --prep_def_merge_tr_red                 false
% 42.85/5.99  --prep_def_merge_tr_cl                  false
% 42.85/5.99  --smt_preprocessing                     true
% 42.85/5.99  --smt_ac_axioms                         fast
% 42.85/5.99  --preprocessed_out                      false
% 42.85/5.99  --preprocessed_stats                    false
% 42.85/5.99  
% 42.85/5.99  ------ Abstraction refinement Options
% 42.85/5.99  
% 42.85/5.99  --abstr_ref                             []
% 42.85/5.99  --abstr_ref_prep                        false
% 42.85/5.99  --abstr_ref_until_sat                   false
% 42.85/5.99  --abstr_ref_sig_restrict                funpre
% 42.85/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 42.85/5.99  --abstr_ref_under                       []
% 42.85/5.99  
% 42.85/5.99  ------ SAT Options
% 42.85/5.99  
% 42.85/5.99  --sat_mode                              false
% 42.85/5.99  --sat_fm_restart_options                ""
% 42.85/5.99  --sat_gr_def                            false
% 42.85/5.99  --sat_epr_types                         true
% 42.85/5.99  --sat_non_cyclic_types                  false
% 42.85/5.99  --sat_finite_models                     false
% 42.85/5.99  --sat_fm_lemmas                         false
% 42.85/5.99  --sat_fm_prep                           false
% 42.85/5.99  --sat_fm_uc_incr                        true
% 42.85/5.99  --sat_out_model                         small
% 42.85/5.99  --sat_out_clauses                       false
% 42.85/5.99  
% 42.85/5.99  ------ QBF Options
% 42.85/5.99  
% 42.85/5.99  --qbf_mode                              false
% 42.85/5.99  --qbf_elim_univ                         false
% 42.85/5.99  --qbf_dom_inst                          none
% 42.85/5.99  --qbf_dom_pre_inst                      false
% 42.85/5.99  --qbf_sk_in                             false
% 42.85/5.99  --qbf_pred_elim                         true
% 42.85/5.99  --qbf_split                             512
% 42.85/5.99  
% 42.85/5.99  ------ BMC1 Options
% 42.85/5.99  
% 42.85/5.99  --bmc1_incremental                      false
% 42.85/5.99  --bmc1_axioms                           reachable_all
% 42.85/5.99  --bmc1_min_bound                        0
% 42.85/5.99  --bmc1_max_bound                        -1
% 42.85/5.99  --bmc1_max_bound_default                -1
% 42.85/5.99  --bmc1_symbol_reachability              true
% 42.85/5.99  --bmc1_property_lemmas                  false
% 42.85/5.99  --bmc1_k_induction                      false
% 42.85/5.99  --bmc1_non_equiv_states                 false
% 42.85/5.99  --bmc1_deadlock                         false
% 42.85/5.99  --bmc1_ucm                              false
% 42.85/5.99  --bmc1_add_unsat_core                   none
% 42.85/5.99  --bmc1_unsat_core_children              false
% 42.85/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 42.85/5.99  --bmc1_out_stat                         full
% 42.85/5.99  --bmc1_ground_init                      false
% 42.85/5.99  --bmc1_pre_inst_next_state              false
% 42.85/5.99  --bmc1_pre_inst_state                   false
% 42.85/5.99  --bmc1_pre_inst_reach_state             false
% 42.85/5.99  --bmc1_out_unsat_core                   false
% 42.85/5.99  --bmc1_aig_witness_out                  false
% 42.85/5.99  --bmc1_verbose                          false
% 42.85/5.99  --bmc1_dump_clauses_tptp                false
% 42.85/5.99  --bmc1_dump_unsat_core_tptp             false
% 42.85/5.99  --bmc1_dump_file                        -
% 42.85/5.99  --bmc1_ucm_expand_uc_limit              128
% 42.85/5.99  --bmc1_ucm_n_expand_iterations          6
% 42.85/5.99  --bmc1_ucm_extend_mode                  1
% 42.85/5.99  --bmc1_ucm_init_mode                    2
% 42.85/5.99  --bmc1_ucm_cone_mode                    none
% 42.85/5.99  --bmc1_ucm_reduced_relation_type        0
% 42.85/5.99  --bmc1_ucm_relax_model                  4
% 42.85/5.99  --bmc1_ucm_full_tr_after_sat            true
% 42.85/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 42.85/5.99  --bmc1_ucm_layered_model                none
% 42.85/5.99  --bmc1_ucm_max_lemma_size               10
% 42.85/5.99  
% 42.85/5.99  ------ AIG Options
% 42.85/5.99  
% 42.85/5.99  --aig_mode                              false
% 42.85/5.99  
% 42.85/5.99  ------ Instantiation Options
% 42.85/5.99  
% 42.85/5.99  --instantiation_flag                    true
% 42.85/5.99  --inst_sos_flag                         true
% 42.85/5.99  --inst_sos_phase                        true
% 42.85/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 42.85/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 42.85/5.99  --inst_lit_sel_side                     num_symb
% 42.85/5.99  --inst_solver_per_active                1400
% 42.85/5.99  --inst_solver_calls_frac                1.
% 42.85/5.99  --inst_passive_queue_type               priority_queues
% 42.85/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 42.85/5.99  --inst_passive_queues_freq              [25;2]
% 42.85/5.99  --inst_dismatching                      true
% 42.85/5.99  --inst_eager_unprocessed_to_passive     true
% 42.85/5.99  --inst_prop_sim_given                   true
% 42.85/5.99  --inst_prop_sim_new                     false
% 42.85/5.99  --inst_subs_new                         false
% 42.85/5.99  --inst_eq_res_simp                      false
% 42.85/5.99  --inst_subs_given                       false
% 42.85/5.99  --inst_orphan_elimination               true
% 42.85/5.99  --inst_learning_loop_flag               true
% 42.85/5.99  --inst_learning_start                   3000
% 42.85/5.99  --inst_learning_factor                  2
% 42.85/5.99  --inst_start_prop_sim_after_learn       3
% 42.85/5.99  --inst_sel_renew                        solver
% 42.85/5.99  --inst_lit_activity_flag                true
% 42.85/5.99  --inst_restr_to_given                   false
% 42.85/5.99  --inst_activity_threshold               500
% 42.85/5.99  --inst_out_proof                        true
% 42.85/5.99  
% 42.85/5.99  ------ Resolution Options
% 42.85/5.99  
% 42.85/5.99  --resolution_flag                       true
% 42.85/5.99  --res_lit_sel                           adaptive
% 42.85/5.99  --res_lit_sel_side                      none
% 42.85/5.99  --res_ordering                          kbo
% 42.85/5.99  --res_to_prop_solver                    active
% 42.85/5.99  --res_prop_simpl_new                    false
% 42.85/5.99  --res_prop_simpl_given                  true
% 42.85/5.99  --res_passive_queue_type                priority_queues
% 42.85/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 42.85/5.99  --res_passive_queues_freq               [15;5]
% 42.85/5.99  --res_forward_subs                      full
% 42.85/5.99  --res_backward_subs                     full
% 42.85/5.99  --res_forward_subs_resolution           true
% 42.85/5.99  --res_backward_subs_resolution          true
% 42.85/5.99  --res_orphan_elimination                true
% 42.85/5.99  --res_time_limit                        2.
% 42.85/5.99  --res_out_proof                         true
% 42.85/5.99  
% 42.85/5.99  ------ Superposition Options
% 42.85/5.99  
% 42.85/5.99  --superposition_flag                    true
% 42.85/5.99  --sup_passive_queue_type                priority_queues
% 42.85/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 42.85/5.99  --sup_passive_queues_freq               [8;1;4]
% 42.85/5.99  --demod_completeness_check              fast
% 42.85/5.99  --demod_use_ground                      true
% 42.85/5.99  --sup_to_prop_solver                    passive
% 42.85/5.99  --sup_prop_simpl_new                    true
% 42.85/5.99  --sup_prop_simpl_given                  true
% 42.85/5.99  --sup_fun_splitting                     true
% 42.85/5.99  --sup_smt_interval                      50000
% 42.85/5.99  
% 42.85/5.99  ------ Superposition Simplification Setup
% 42.85/5.99  
% 42.85/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 42.85/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 42.85/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 42.85/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 42.85/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 42.85/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 42.85/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 42.85/5.99  --sup_immed_triv                        [TrivRules]
% 42.85/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 42.85/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 42.85/5.99  --sup_immed_bw_main                     []
% 42.85/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 42.85/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 42.85/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 42.85/5.99  --sup_input_bw                          []
% 42.85/5.99  
% 42.85/5.99  ------ Combination Options
% 42.85/5.99  
% 42.85/5.99  --comb_res_mult                         3
% 42.85/5.99  --comb_sup_mult                         2
% 42.85/5.99  --comb_inst_mult                        10
% 42.85/5.99  
% 42.85/5.99  ------ Debug Options
% 42.85/5.99  
% 42.85/5.99  --dbg_backtrace                         false
% 42.85/5.99  --dbg_dump_prop_clauses                 false
% 42.85/5.99  --dbg_dump_prop_clauses_file            -
% 42.85/5.99  --dbg_out_stat                          false
% 42.85/5.99  ------ Parsing...
% 42.85/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 42.85/5.99  
% 42.85/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 42.85/5.99  
% 42.85/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 42.85/5.99  
% 42.85/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 42.85/5.99  ------ Proving...
% 42.85/5.99  ------ Problem Properties 
% 42.85/5.99  
% 42.85/5.99  
% 42.85/5.99  clauses                                 30
% 42.85/5.99  conjectures                             2
% 42.85/5.99  EPR                                     4
% 42.85/5.99  Horn                                    29
% 42.85/5.99  unary                                   12
% 42.85/5.99  binary                                  13
% 42.85/5.99  lits                                    53
% 42.85/5.99  lits eq                                 21
% 42.85/5.99  fd_pure                                 0
% 42.85/5.99  fd_pseudo                               0
% 42.85/5.99  fd_cond                                 0
% 42.85/5.99  fd_pseudo_cond                          3
% 42.85/5.99  AC symbols                              0
% 42.85/5.99  
% 42.85/5.99  ------ Schedule dynamic 5 is on 
% 42.85/5.99  
% 42.85/5.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 42.85/5.99  
% 42.85/5.99  
% 42.85/5.99  ------ 
% 42.85/5.99  Current options:
% 42.85/5.99  ------ 
% 42.85/5.99  
% 42.85/5.99  ------ Input Options
% 42.85/5.99  
% 42.85/5.99  --out_options                           all
% 42.85/5.99  --tptp_safe_out                         true
% 42.85/5.99  --problem_path                          ""
% 42.85/5.99  --include_path                          ""
% 42.85/5.99  --clausifier                            res/vclausify_rel
% 42.85/5.99  --clausifier_options                    ""
% 42.85/5.99  --stdin                                 false
% 42.85/5.99  --stats_out                             all
% 42.85/5.99  
% 42.85/5.99  ------ General Options
% 42.85/5.99  
% 42.85/5.99  --fof                                   false
% 42.85/5.99  --time_out_real                         305.
% 42.85/5.99  --time_out_virtual                      -1.
% 42.85/5.99  --symbol_type_check                     false
% 42.85/5.99  --clausify_out                          false
% 42.85/5.99  --sig_cnt_out                           false
% 42.85/5.99  --trig_cnt_out                          false
% 42.85/5.99  --trig_cnt_out_tolerance                1.
% 42.85/5.99  --trig_cnt_out_sk_spl                   false
% 42.85/5.99  --abstr_cl_out                          false
% 42.85/5.99  
% 42.85/5.99  ------ Global Options
% 42.85/5.99  
% 42.85/5.99  --schedule                              default
% 42.85/5.99  --add_important_lit                     false
% 42.85/5.99  --prop_solver_per_cl                    1000
% 42.85/5.99  --min_unsat_core                        false
% 42.85/5.99  --soft_assumptions                      false
% 42.85/5.99  --soft_lemma_size                       3
% 42.85/5.99  --prop_impl_unit_size                   0
% 42.85/5.99  --prop_impl_unit                        []
% 42.85/5.99  --share_sel_clauses                     true
% 42.85/5.99  --reset_solvers                         false
% 42.85/5.99  --bc_imp_inh                            [conj_cone]
% 42.85/5.99  --conj_cone_tolerance                   3.
% 42.85/5.99  --extra_neg_conj                        none
% 42.85/5.99  --large_theory_mode                     true
% 42.85/5.99  --prolific_symb_bound                   200
% 42.85/5.99  --lt_threshold                          2000
% 42.85/5.99  --clause_weak_htbl                      true
% 42.85/5.99  --gc_record_bc_elim                     false
% 42.85/5.99  
% 42.85/5.99  ------ Preprocessing Options
% 42.85/5.99  
% 42.85/5.99  --preprocessing_flag                    true
% 42.85/5.99  --time_out_prep_mult                    0.1
% 42.85/5.99  --splitting_mode                        input
% 42.85/5.99  --splitting_grd                         true
% 42.85/5.99  --splitting_cvd                         false
% 42.85/5.99  --splitting_cvd_svl                     false
% 42.85/5.99  --splitting_nvd                         32
% 42.85/5.99  --sub_typing                            true
% 42.85/5.99  --prep_gs_sim                           true
% 42.85/5.99  --prep_unflatten                        true
% 42.85/5.99  --prep_res_sim                          true
% 42.85/5.99  --prep_upred                            true
% 42.85/5.99  --prep_sem_filter                       exhaustive
% 42.85/5.99  --prep_sem_filter_out                   false
% 42.85/5.99  --pred_elim                             true
% 42.85/5.99  --res_sim_input                         true
% 42.85/5.99  --eq_ax_congr_red                       true
% 42.85/5.99  --pure_diseq_elim                       true
% 42.85/5.99  --brand_transform                       false
% 42.85/5.99  --non_eq_to_eq                          false
% 42.85/5.99  --prep_def_merge                        true
% 42.85/5.99  --prep_def_merge_prop_impl              false
% 42.85/5.99  --prep_def_merge_mbd                    true
% 42.85/5.99  --prep_def_merge_tr_red                 false
% 42.85/5.99  --prep_def_merge_tr_cl                  false
% 42.85/5.99  --smt_preprocessing                     true
% 42.85/5.99  --smt_ac_axioms                         fast
% 42.85/5.99  --preprocessed_out                      false
% 42.85/5.99  --preprocessed_stats                    false
% 42.85/5.99  
% 42.85/5.99  ------ Abstraction refinement Options
% 42.85/5.99  
% 42.85/5.99  --abstr_ref                             []
% 42.85/5.99  --abstr_ref_prep                        false
% 42.85/5.99  --abstr_ref_until_sat                   false
% 42.85/5.99  --abstr_ref_sig_restrict                funpre
% 42.85/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 42.85/5.99  --abstr_ref_under                       []
% 42.85/5.99  
% 42.85/5.99  ------ SAT Options
% 42.85/5.99  
% 42.85/5.99  --sat_mode                              false
% 42.85/5.99  --sat_fm_restart_options                ""
% 42.85/5.99  --sat_gr_def                            false
% 42.85/5.99  --sat_epr_types                         true
% 42.85/5.99  --sat_non_cyclic_types                  false
% 42.85/5.99  --sat_finite_models                     false
% 42.85/5.99  --sat_fm_lemmas                         false
% 42.85/5.99  --sat_fm_prep                           false
% 42.85/5.99  --sat_fm_uc_incr                        true
% 42.85/5.99  --sat_out_model                         small
% 42.85/5.99  --sat_out_clauses                       false
% 42.85/5.99  
% 42.85/5.99  ------ QBF Options
% 42.85/5.99  
% 42.85/5.99  --qbf_mode                              false
% 42.85/5.99  --qbf_elim_univ                         false
% 42.85/5.99  --qbf_dom_inst                          none
% 42.85/5.99  --qbf_dom_pre_inst                      false
% 42.85/5.99  --qbf_sk_in                             false
% 42.85/5.99  --qbf_pred_elim                         true
% 42.85/5.99  --qbf_split                             512
% 42.85/5.99  
% 42.85/5.99  ------ BMC1 Options
% 42.85/5.99  
% 42.85/5.99  --bmc1_incremental                      false
% 42.85/5.99  --bmc1_axioms                           reachable_all
% 42.85/5.99  --bmc1_min_bound                        0
% 42.85/5.99  --bmc1_max_bound                        -1
% 42.85/5.99  --bmc1_max_bound_default                -1
% 42.85/5.99  --bmc1_symbol_reachability              true
% 42.85/5.99  --bmc1_property_lemmas                  false
% 42.85/5.99  --bmc1_k_induction                      false
% 42.85/5.99  --bmc1_non_equiv_states                 false
% 42.85/5.99  --bmc1_deadlock                         false
% 42.85/5.99  --bmc1_ucm                              false
% 42.85/5.99  --bmc1_add_unsat_core                   none
% 42.85/5.99  --bmc1_unsat_core_children              false
% 42.85/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 42.85/5.99  --bmc1_out_stat                         full
% 42.85/5.99  --bmc1_ground_init                      false
% 42.85/5.99  --bmc1_pre_inst_next_state              false
% 42.85/5.99  --bmc1_pre_inst_state                   false
% 42.85/5.99  --bmc1_pre_inst_reach_state             false
% 42.85/5.99  --bmc1_out_unsat_core                   false
% 42.85/5.99  --bmc1_aig_witness_out                  false
% 42.85/5.99  --bmc1_verbose                          false
% 42.85/5.99  --bmc1_dump_clauses_tptp                false
% 42.85/5.99  --bmc1_dump_unsat_core_tptp             false
% 42.85/5.99  --bmc1_dump_file                        -
% 42.85/5.99  --bmc1_ucm_expand_uc_limit              128
% 42.85/5.99  --bmc1_ucm_n_expand_iterations          6
% 42.85/5.99  --bmc1_ucm_extend_mode                  1
% 42.85/5.99  --bmc1_ucm_init_mode                    2
% 42.85/5.99  --bmc1_ucm_cone_mode                    none
% 42.85/5.99  --bmc1_ucm_reduced_relation_type        0
% 42.85/5.99  --bmc1_ucm_relax_model                  4
% 42.85/5.99  --bmc1_ucm_full_tr_after_sat            true
% 42.85/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 42.85/5.99  --bmc1_ucm_layered_model                none
% 42.85/5.99  --bmc1_ucm_max_lemma_size               10
% 42.85/5.99  
% 42.85/5.99  ------ AIG Options
% 42.85/5.99  
% 42.85/5.99  --aig_mode                              false
% 42.85/5.99  
% 42.85/5.99  ------ Instantiation Options
% 42.85/5.99  
% 42.85/5.99  --instantiation_flag                    true
% 42.85/5.99  --inst_sos_flag                         true
% 42.85/5.99  --inst_sos_phase                        true
% 42.85/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 42.85/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 42.85/5.99  --inst_lit_sel_side                     none
% 42.85/5.99  --inst_solver_per_active                1400
% 42.85/5.99  --inst_solver_calls_frac                1.
% 42.85/5.99  --inst_passive_queue_type               priority_queues
% 42.85/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 42.85/5.99  --inst_passive_queues_freq              [25;2]
% 42.85/5.99  --inst_dismatching                      true
% 42.85/5.99  --inst_eager_unprocessed_to_passive     true
% 42.85/5.99  --inst_prop_sim_given                   true
% 42.85/5.99  --inst_prop_sim_new                     false
% 42.85/5.99  --inst_subs_new                         false
% 42.85/5.99  --inst_eq_res_simp                      false
% 42.85/5.99  --inst_subs_given                       false
% 42.85/5.99  --inst_orphan_elimination               true
% 42.85/5.99  --inst_learning_loop_flag               true
% 42.85/5.99  --inst_learning_start                   3000
% 42.85/5.99  --inst_learning_factor                  2
% 42.85/5.99  --inst_start_prop_sim_after_learn       3
% 42.85/5.99  --inst_sel_renew                        solver
% 42.85/5.99  --inst_lit_activity_flag                true
% 42.85/5.99  --inst_restr_to_given                   false
% 42.85/5.99  --inst_activity_threshold               500
% 42.85/5.99  --inst_out_proof                        true
% 42.85/5.99  
% 42.85/5.99  ------ Resolution Options
% 42.85/5.99  
% 42.85/5.99  --resolution_flag                       false
% 42.85/5.99  --res_lit_sel                           adaptive
% 42.85/5.99  --res_lit_sel_side                      none
% 42.85/5.99  --res_ordering                          kbo
% 42.85/5.99  --res_to_prop_solver                    active
% 42.85/5.99  --res_prop_simpl_new                    false
% 42.85/5.99  --res_prop_simpl_given                  true
% 42.85/5.99  --res_passive_queue_type                priority_queues
% 42.85/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 42.85/5.99  --res_passive_queues_freq               [15;5]
% 42.85/5.99  --res_forward_subs                      full
% 42.85/5.99  --res_backward_subs                     full
% 42.85/5.99  --res_forward_subs_resolution           true
% 42.85/5.99  --res_backward_subs_resolution          true
% 42.85/5.99  --res_orphan_elimination                true
% 42.85/5.99  --res_time_limit                        2.
% 42.85/5.99  --res_out_proof                         true
% 42.85/5.99  
% 42.85/5.99  ------ Superposition Options
% 42.85/5.99  
% 42.85/5.99  --superposition_flag                    true
% 42.85/5.99  --sup_passive_queue_type                priority_queues
% 42.85/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 42.85/5.99  --sup_passive_queues_freq               [8;1;4]
% 42.85/5.99  --demod_completeness_check              fast
% 42.85/5.99  --demod_use_ground                      true
% 42.85/5.99  --sup_to_prop_solver                    passive
% 42.85/5.99  --sup_prop_simpl_new                    true
% 42.85/5.99  --sup_prop_simpl_given                  true
% 42.85/5.99  --sup_fun_splitting                     true
% 42.85/5.99  --sup_smt_interval                      50000
% 42.85/5.99  
% 42.85/5.99  ------ Superposition Simplification Setup
% 42.85/5.99  
% 42.85/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 42.85/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 42.85/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 42.85/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 42.85/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 42.85/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 42.85/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 42.85/5.99  --sup_immed_triv                        [TrivRules]
% 42.85/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 42.85/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 42.85/5.99  --sup_immed_bw_main                     []
% 42.85/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 42.85/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 42.85/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 42.85/5.99  --sup_input_bw                          []
% 42.85/5.99  
% 42.85/5.99  ------ Combination Options
% 42.85/5.99  
% 42.85/5.99  --comb_res_mult                         3
% 42.85/5.99  --comb_sup_mult                         2
% 42.85/5.99  --comb_inst_mult                        10
% 42.85/5.99  
% 42.85/5.99  ------ Debug Options
% 42.85/5.99  
% 42.85/5.99  --dbg_backtrace                         false
% 42.85/5.99  --dbg_dump_prop_clauses                 false
% 42.85/5.99  --dbg_dump_prop_clauses_file            -
% 42.85/5.99  --dbg_out_stat                          false
% 42.85/5.99  
% 42.85/5.99  
% 42.85/5.99  
% 42.85/5.99  
% 42.85/5.99  ------ Proving...
% 42.85/5.99  
% 42.85/5.99  
% 42.85/5.99  % SZS status Theorem for theBenchmark.p
% 42.85/5.99  
% 42.85/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 42.85/5.99  
% 42.85/5.99  fof(f3,axiom,(
% 42.85/5.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 42.85/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.85/5.99  
% 42.85/5.99  fof(f34,plain,(
% 42.85/5.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 42.85/5.99    inference(nnf_transformation,[],[f3])).
% 42.85/5.99  
% 42.85/5.99  fof(f35,plain,(
% 42.85/5.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 42.85/5.99    inference(flattening,[],[f34])).
% 42.85/5.99  
% 42.85/5.99  fof(f46,plain,(
% 42.85/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 42.85/5.99    inference(cnf_transformation,[],[f35])).
% 42.85/5.99  
% 42.85/5.99  fof(f79,plain,(
% 42.85/5.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 42.85/5.99    inference(equality_resolution,[],[f46])).
% 42.85/5.99  
% 42.85/5.99  fof(f16,axiom,(
% 42.85/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 42.85/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.85/5.99  
% 42.85/5.99  fof(f30,plain,(
% 42.85/5.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.85/5.99    inference(ennf_transformation,[],[f16])).
% 42.85/5.99  
% 42.85/5.99  fof(f68,plain,(
% 42.85/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.85/5.99    inference(cnf_transformation,[],[f30])).
% 42.85/5.99  
% 42.85/5.99  fof(f20,conjecture,(
% 42.85/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 42.85/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.85/5.99  
% 42.85/5.99  fof(f21,negated_conjecture,(
% 42.85/5.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 42.85/5.99    inference(negated_conjecture,[],[f20])).
% 42.85/5.99  
% 42.85/5.99  fof(f32,plain,(
% 42.85/5.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.85/5.99    inference(ennf_transformation,[],[f21])).
% 42.85/5.99  
% 42.85/5.99  fof(f33,plain,(
% 42.85/5.99    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.85/5.99    inference(flattening,[],[f32])).
% 42.85/5.99  
% 42.85/5.99  fof(f42,plain,(
% 42.85/5.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(sK3,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 43.44/5.99    introduced(choice_axiom,[])).
% 43.44/5.99  
% 43.44/5.99  fof(f41,plain,(
% 43.44/5.99    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 43.44/5.99    introduced(choice_axiom,[])).
% 43.44/5.99  
% 43.44/5.99  fof(f43,plain,(
% 43.44/5.99    (~r1_tarski(sK3,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 43.44/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42,f41])).
% 43.44/5.99  
% 43.44/5.99  fof(f73,plain,(
% 43.44/5.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 43.44/5.99    inference(cnf_transformation,[],[f43])).
% 43.44/5.99  
% 43.44/5.99  fof(f74,plain,(
% 43.44/5.99    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 43.44/5.99    inference(cnf_transformation,[],[f43])).
% 43.44/5.99  
% 43.44/5.99  fof(f5,axiom,(
% 43.44/5.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f22,plain,(
% 43.44/5.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 43.44/5.99    inference(ennf_transformation,[],[f5])).
% 43.44/5.99  
% 43.44/5.99  fof(f51,plain,(
% 43.44/5.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 43.44/5.99    inference(cnf_transformation,[],[f22])).
% 43.44/5.99  
% 43.44/5.99  fof(f13,axiom,(
% 43.44/5.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f27,plain,(
% 43.44/5.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 43.44/5.99    inference(ennf_transformation,[],[f13])).
% 43.44/5.99  
% 43.44/5.99  fof(f28,plain,(
% 43.44/5.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 43.44/5.99    inference(flattening,[],[f27])).
% 43.44/5.99  
% 43.44/5.99  fof(f59,plain,(
% 43.44/5.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f28])).
% 43.44/5.99  
% 43.44/5.99  fof(f6,axiom,(
% 43.44/5.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f23,plain,(
% 43.44/5.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 43.44/5.99    inference(ennf_transformation,[],[f6])).
% 43.44/5.99  
% 43.44/5.99  fof(f52,plain,(
% 43.44/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f23])).
% 43.44/5.99  
% 43.44/5.99  fof(f9,axiom,(
% 43.44/5.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f55,plain,(
% 43.44/5.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f9])).
% 43.44/5.99  
% 43.44/5.99  fof(f1,axiom,(
% 43.44/5.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f44,plain,(
% 43.44/5.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f1])).
% 43.44/5.99  
% 43.44/5.99  fof(f2,axiom,(
% 43.44/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f45,plain,(
% 43.44/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f2])).
% 43.44/5.99  
% 43.44/5.99  fof(f11,axiom,(
% 43.44/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f57,plain,(
% 43.44/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.44/5.99    inference(cnf_transformation,[],[f11])).
% 43.44/5.99  
% 43.44/5.99  fof(f77,plain,(
% 43.44/5.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 43.44/5.99    inference(definition_unfolding,[],[f45,f57,f57])).
% 43.44/5.99  
% 43.44/5.99  fof(f15,axiom,(
% 43.44/5.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f29,plain,(
% 43.44/5.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 43.44/5.99    inference(ennf_transformation,[],[f15])).
% 43.44/5.99  
% 43.44/5.99  fof(f40,plain,(
% 43.44/5.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 43.44/5.99    inference(nnf_transformation,[],[f29])).
% 43.44/5.99  
% 43.44/5.99  fof(f65,plain,(
% 43.44/5.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f40])).
% 43.44/5.99  
% 43.44/5.99  fof(f14,axiom,(
% 43.44/5.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f36,plain,(
% 43.44/5.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 43.44/5.99    inference(nnf_transformation,[],[f14])).
% 43.44/5.99  
% 43.44/5.99  fof(f37,plain,(
% 43.44/5.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 43.44/5.99    inference(rectify,[],[f36])).
% 43.44/5.99  
% 43.44/5.99  fof(f38,plain,(
% 43.44/5.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 43.44/5.99    introduced(choice_axiom,[])).
% 43.44/5.99  
% 43.44/5.99  fof(f39,plain,(
% 43.44/5.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 43.44/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 43.44/5.99  
% 43.44/5.99  fof(f60,plain,(
% 43.44/5.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 43.44/5.99    inference(cnf_transformation,[],[f39])).
% 43.44/5.99  
% 43.44/5.99  fof(f81,plain,(
% 43.44/5.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 43.44/5.99    inference(equality_resolution,[],[f60])).
% 43.44/5.99  
% 43.44/5.99  fof(f61,plain,(
% 43.44/5.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 43.44/5.99    inference(cnf_transformation,[],[f39])).
% 43.44/5.99  
% 43.44/5.99  fof(f80,plain,(
% 43.44/5.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 43.44/5.99    inference(equality_resolution,[],[f61])).
% 43.44/5.99  
% 43.44/5.99  fof(f17,axiom,(
% 43.44/5.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f69,plain,(
% 43.44/5.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 43.44/5.99    inference(cnf_transformation,[],[f17])).
% 43.44/5.99  
% 43.44/5.99  fof(f18,axiom,(
% 43.44/5.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f31,plain,(
% 43.44/5.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.44/5.99    inference(ennf_transformation,[],[f18])).
% 43.44/5.99  
% 43.44/5.99  fof(f70,plain,(
% 43.44/5.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.44/5.99    inference(cnf_transformation,[],[f31])).
% 43.44/5.99  
% 43.44/5.99  fof(f72,plain,(
% 43.44/5.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 43.44/5.99    inference(cnf_transformation,[],[f43])).
% 43.44/5.99  
% 43.44/5.99  fof(f12,axiom,(
% 43.44/5.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f58,plain,(
% 43.44/5.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 43.44/5.99    inference(cnf_transformation,[],[f12])).
% 43.44/5.99  
% 43.44/5.99  fof(f64,plain,(
% 43.44/5.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f40])).
% 43.44/5.99  
% 43.44/5.99  fof(f7,axiom,(
% 43.44/5.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f24,plain,(
% 43.44/5.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.44/5.99    inference(ennf_transformation,[],[f7])).
% 43.44/5.99  
% 43.44/5.99  fof(f25,plain,(
% 43.44/5.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 43.44/5.99    inference(flattening,[],[f24])).
% 43.44/5.99  
% 43.44/5.99  fof(f53,plain,(
% 43.44/5.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f25])).
% 43.44/5.99  
% 43.44/5.99  fof(f10,axiom,(
% 43.44/5.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f26,plain,(
% 43.44/5.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 43.44/5.99    inference(ennf_transformation,[],[f10])).
% 43.44/5.99  
% 43.44/5.99  fof(f56,plain,(
% 43.44/5.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 43.44/5.99    inference(cnf_transformation,[],[f26])).
% 43.44/5.99  
% 43.44/5.99  fof(f8,axiom,(
% 43.44/5.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 43.44/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.44/5.99  
% 43.44/5.99  fof(f54,plain,(
% 43.44/5.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f8])).
% 43.44/5.99  
% 43.44/5.99  fof(f48,plain,(
% 43.44/5.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 43.44/5.99    inference(cnf_transformation,[],[f35])).
% 43.44/5.99  
% 43.44/5.99  fof(f75,plain,(
% 43.44/5.99    ~r1_tarski(sK3,k3_subset_1(sK1,sK2))),
% 43.44/5.99    inference(cnf_transformation,[],[f43])).
% 43.44/5.99  
% 43.44/5.99  cnf(c_5,plain,
% 43.44/5.99      ( r1_tarski(X0,X0) ),
% 43.44/5.99      inference(cnf_transformation,[],[f79]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1632,plain,
% 43.44/5.99      ( r1_tarski(X0,X0) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_23,plain,
% 43.44/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.44/5.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 43.44/5.99      inference(cnf_transformation,[],[f68]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_29,negated_conjecture,
% 43.44/5.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f73]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_626,plain,
% 43.44/5.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 43.44/5.99      | sK3 != X1 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_627,plain,
% 43.44/5.99      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_626]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1926,plain,
% 43.44/5.99      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 43.44/5.99      inference(equality_resolution,[status(thm)],[c_627]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_28,negated_conjecture,
% 43.44/5.99      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f74]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1619,plain,
% 43.44/5.99      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2734,plain,
% 43.44/5.99      ( r1_tarski(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 43.44/5.99      inference(demodulation,[status(thm)],[c_1926,c_1619]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_6,plain,
% 43.44/5.99      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f51]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_14,plain,
% 43.44/5.99      ( ~ r1_xboole_0(X0,X1)
% 43.44/5.99      | ~ r1_tarski(X0,X2)
% 43.44/5.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f59]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_367,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1)
% 43.44/5.99      | ~ r1_tarski(X0,k4_xboole_0(X2,X3))
% 43.44/5.99      | r1_tarski(X0,k4_xboole_0(X1,X3)) ),
% 43.44/5.99      inference(resolution,[status(thm)],[c_6,c_14]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1618,plain,
% 43.44/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.44/5.99      | r1_tarski(X0,k4_xboole_0(X2,X3)) != iProver_top
% 43.44/5.99      | r1_tarski(X0,k4_xboole_0(X1,X3)) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_6574,plain,
% 43.44/5.99      ( r1_tarski(sK2,X0) != iProver_top
% 43.44/5.99      | r1_tarski(sK2,k4_xboole_0(X0,sK3)) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_2734,c_1618]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_8,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 43.44/5.99      inference(cnf_transformation,[],[f52]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1630,plain,
% 43.44/5.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_7122,plain,
% 43.44/5.99      ( k2_xboole_0(sK2,k4_xboole_0(X0,sK3)) = k4_xboole_0(X0,sK3)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_1630]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_7268,plain,
% 43.44/5.99      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK3) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1632,c_7122]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_11,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 43.44/5.99      inference(cnf_transformation,[],[f55]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1627,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_3612,plain,
% 43.44/5.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1627,c_1630]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1,plain,
% 43.44/5.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 43.44/5.99      inference(cnf_transformation,[],[f44]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_5246,plain,
% 43.44/5.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_3612,c_1]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_7274,plain,
% 43.44/5.99      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 43.44/5.99      inference(demodulation,[status(thm)],[c_7268,c_5246]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2,plain,
% 43.44/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f77]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_36908,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_7274,c_2]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_21,plain,
% 43.44/5.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 43.44/5.99      inference(cnf_transformation,[],[f65]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_522,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,X1)
% 43.44/5.99      | v1_xboole_0(X1)
% 43.44/5.99      | X2 != X0
% 43.44/5.99      | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
% 43.44/5.99      | k1_zfmisc_1(X3) != X1 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_523,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 43.44/5.99      | v1_xboole_0(k1_zfmisc_1(X1))
% 43.44/5.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_522]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_18,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.44/5.99      inference(cnf_transformation,[],[f81]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_17,plain,
% 43.44/5.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.44/5.99      inference(cnf_transformation,[],[f80]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_225,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 43.44/5.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_226,plain,
% 43.44/5.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.44/5.99      inference(renaming,[status(thm)],[c_225]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_452,plain,
% 43.44/5.99      ( m1_subset_1(X0,X1)
% 43.44/5.99      | ~ r1_tarski(X2,X3)
% 43.44/5.99      | v1_xboole_0(X1)
% 43.44/5.99      | X0 != X2
% 43.44/5.99      | k1_zfmisc_1(X3) != X1 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_226,c_21]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_453,plain,
% 43.44/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.44/5.99      | ~ r1_tarski(X0,X1)
% 43.44/5.99      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_452]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_24,plain,
% 43.44/5.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f69]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_463,plain,
% 43.44/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.44/5.99      inference(forward_subsumption_resolution,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_453,c_24]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_527,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 43.44/5.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 43.44/5.99      inference(global_propositional_subsumption,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_523,c_23,c_18,c_463]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_931,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 43.44/5.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_932,plain,
% 43.44/5.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.44/5.99      inference(renaming,[status(thm)],[c_931]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_977,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 43.44/5.99      inference(bin_hyper_res,[status(thm)],[c_527,c_932]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1614,plain,
% 43.44/5.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 43.44/5.99      | r1_tarski(X1,X0) != iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_7120,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(X0,sK3),sK2) = k4_xboole_0(k4_xboole_0(X0,sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_1614]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_7798,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_7120]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_10637,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_7798]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_11610,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_10637]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_11805,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_11610]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_12249,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_11805]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_13118,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_12249]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_13364,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_13118]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_13862,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_13364]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_14721,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_13862]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_14995,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_14721]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_16862,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_14995]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_17123,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_16862]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_17429,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_17123]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_18074,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_17429]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_18191,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_18074]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_18396,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_18191]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_18819,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_18396]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_19408,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_18819]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_20563,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_19408]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_20699,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_20563]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_20976,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_20699]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_21624,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_20976]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_22293,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_21624]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_22482,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2)
% 43.44/5.99      | r1_tarski(sK2,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6574,c_22293]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_24601,plain,
% 43.44/5.99      ( k3_subset_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK3),sK2) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1632,c_22482]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_5464,plain,
% 43.44/5.99      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1627,c_1614]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_25,plain,
% 43.44/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.44/5.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.44/5.99      inference(cnf_transformation,[],[f70]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_30,negated_conjecture,
% 43.44/5.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f72]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_635,plain,
% 43.44/5.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 43.44/5.99      | sK2 != X1 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_636,plain,
% 43.44/5.99      ( k3_subset_1(X0,k3_subset_1(X0,sK2)) = sK2
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_635]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2052,plain,
% 43.44/5.99      ( k3_subset_1(sK1,k3_subset_1(sK1,sK2)) = sK2 ),
% 43.44/5.99      inference(equality_resolution,[status(thm)],[c_636]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_644,plain,
% 43.44/5.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 43.44/5.99      | sK2 != X1 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_645,plain,
% 43.44/5.99      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_644]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2053,plain,
% 43.44/5.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 43.44/5.99      inference(equality_resolution,[status(thm)],[c_645]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2736,plain,
% 43.44/5.99      ( k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 43.44/5.99      inference(light_normalisation,[status(thm)],[c_2052,c_2052,c_2053]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_22686,plain,
% 43.44/5.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_5464,c_2736]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_504,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,X1)
% 43.44/5.99      | v1_xboole_0(X1)
% 43.44/5.99      | X2 != X0
% 43.44/5.99      | k3_subset_1(X3,k3_subset_1(X3,X2)) = X2
% 43.44/5.99      | k1_zfmisc_1(X3) != X1 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_505,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 43.44/5.99      | v1_xboole_0(k1_zfmisc_1(X1))
% 43.44/5.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_504]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_509,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 43.44/5.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.44/5.99      inference(global_propositional_subsumption,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_505,c_25,c_18,c_463]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_976,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.44/5.99      inference(bin_hyper_res,[status(thm)],[c_509,c_932]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1613,plain,
% 43.44/5.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 43.44/5.99      | r1_tarski(X1,X0) != iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_976]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_4041,plain,
% 43.44/5.99      ( k3_subset_1(X0,k3_subset_1(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1627,c_1613]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_10793,plain,
% 43.44/5.99      ( k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.44/5.99      inference(light_normalisation,[status(thm)],[c_4041,c_4041,c_5464]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_10795,plain,
% 43.44/5.99      ( k3_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_2,c_10793]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_23769,plain,
% 43.44/5.99      ( k3_subset_1(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_22686,c_10795]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_24610,plain,
% 43.44/5.99      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
% 43.44/5.99      inference(light_normalisation,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_24601,c_7274,c_23769]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_36964,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK1) ),
% 43.44/5.99      inference(light_normalisation,[status(thm)],[c_36908,c_24610]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_13,plain,
% 43.44/5.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f58]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1625,plain,
% 43.44/5.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_22,plain,
% 43.44/5.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 43.44/5.99      inference(cnf_transformation,[],[f64]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_581,plain,
% 43.44/5.99      ( r2_hidden(X0,X1)
% 43.44/5.99      | v1_xboole_0(X1)
% 43.44/5.99      | k1_zfmisc_1(sK1) != X1
% 43.44/5.99      | sK2 != X0 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_582,plain,
% 43.44/5.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_581]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_42,plain,
% 43.44/5.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_24]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_584,plain,
% 43.44/5.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 43.44/5.99      inference(global_propositional_subsumption,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_582,c_42]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1615,plain,
% 43.44/5.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1621,plain,
% 43.44/5.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.44/5.99      | r1_tarski(X0,X1) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_4053,plain,
% 43.44/5.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1615,c_1621]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_9,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 43.44/5.99      inference(cnf_transformation,[],[f53]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1629,plain,
% 43.44/5.99      ( r1_tarski(X0,X1) != iProver_top
% 43.44/5.99      | r1_tarski(X1,X2) != iProver_top
% 43.44/5.99      | r1_tarski(X0,X2) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_8899,plain,
% 43.44/5.99      ( r1_tarski(sK2,X0) = iProver_top
% 43.44/5.99      | r1_tarski(sK1,X0) != iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_4053,c_1629]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_9374,plain,
% 43.44/5.99      ( r1_tarski(sK2,k2_xboole_0(sK1,X0)) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1625,c_8899]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_12,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 43.44/5.99      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 43.44/5.99      inference(cnf_transformation,[],[f56]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1626,plain,
% 43.44/5.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 43.44/5.99      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_39785,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(sK2,sK1),X0) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_9374,c_1626]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_61136,plain,
% 43.44/5.99      ( k2_xboole_0(k4_xboole_0(sK2,sK1),X0) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_39785,c_1630]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_10,plain,
% 43.44/5.99      ( r1_tarski(k1_xboole_0,X0) ),
% 43.44/5.99      inference(cnf_transformation,[],[f54]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1628,plain,
% 43.44/5.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_3611,plain,
% 43.44/5.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1628,c_1630]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_3921,plain,
% 43.44/5.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_3611,c_1]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_61182,plain,
% 43.44/5.99      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_61136,c_3921]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_74130,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 43.44/5.99      inference(light_normalisation,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_36964,c_36964,c_61182]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_3324,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_2,c_1627]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_6575,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X3) != iProver_top
% 43.44/5.99      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X3,X2)) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_3324,c_1618]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_74429,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))),X0) != iProver_top
% 43.44/5.99      | r1_tarski(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(X0,sK2)) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_74130,c_6575]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_6779,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1625,c_1626]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_39300,plain,
% 43.44/5.99      ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_6779,c_1630]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_58161,plain,
% 43.44/5.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_39300,c_3921]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_617,plain,
% 43.44/5.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 43.44/5.99      | sK3 != X1 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_618,plain,
% 43.44/5.99      ( k3_subset_1(X0,k3_subset_1(X0,sK3)) = sK3
% 43.44/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_617]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1925,plain,
% 43.44/5.99      ( k3_subset_1(sK1,k3_subset_1(sK1,sK3)) = sK3 ),
% 43.44/5.99      inference(equality_resolution,[status(thm)],[c_618]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2634,plain,
% 43.44/5.99      ( k3_subset_1(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
% 43.44/5.99      inference(light_normalisation,[status(thm)],[c_1925,c_1925,c_1926]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_22685,plain,
% 43.44/5.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_5464,c_2634]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_23438,plain,
% 43.44/5.99      ( k3_subset_1(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_22685,c_10795]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_5462,plain,
% 43.44/5.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1632,c_1614]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_23485,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
% 43.44/5.99      inference(demodulation,[status(thm)],[c_23438,c_5462]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_23448,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_22685,c_2]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_23491,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = sK3 ),
% 43.44/5.99      inference(demodulation,[status(thm)],[c_23485,c_23448]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_58175,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
% 43.44/5.99      inference(demodulation,[status(thm)],[c_58161,c_23491]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_5643,plain,
% 43.44/5.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_2,c_5246]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_74293,plain,
% 43.44/5.99      ( k2_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(sK3,sK2) ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_74130,c_5643]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_74704,plain,
% 43.44/5.99      ( k2_xboole_0(k4_xboole_0(sK3,sK2),sK3) = k4_xboole_0(sK3,sK2) ),
% 43.44/5.99      inference(light_normalisation,[status(thm)],[c_74293,c_58175]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_74705,plain,
% 43.44/5.99      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 43.44/5.99      inference(demodulation,[status(thm)],[c_74704,c_3612]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_74804,plain,
% 43.44/5.99      ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)),X0) != iProver_top
% 43.44/5.99      | r1_tarski(sK3,k4_xboole_0(X0,sK2)) = iProver_top ),
% 43.44/5.99      inference(light_normalisation,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_74429,c_58175,c_74705]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_4039,plain,
% 43.44/5.99      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_1632,c_1613]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_6313,plain,
% 43.44/5.99      ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
% 43.44/5.99      inference(light_normalisation,[status(thm)],[c_4039,c_4039,c_5462]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_22690,plain,
% 43.44/5.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 43.44/5.99      inference(superposition,[status(thm)],[c_5464,c_6313]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_74805,plain,
% 43.44/5.99      ( r1_tarski(sK3,X0) != iProver_top
% 43.44/5.99      | r1_tarski(sK3,k4_xboole_0(X0,sK2)) = iProver_top ),
% 43.44/5.99      inference(demodulation,[status(thm)],[c_74804,c_22690]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_75117,plain,
% 43.44/5.99      ( r1_tarski(sK3,k4_xboole_0(sK1,sK2)) = iProver_top
% 43.44/5.99      | r1_tarski(sK3,sK1) != iProver_top ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_74805]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1163,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.44/5.99      theory(equality) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1672,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1)
% 43.44/5.99      | r1_tarski(sK3,k3_subset_1(sK1,sK2))
% 43.44/5.99      | k3_subset_1(sK1,sK2) != X1
% 43.44/5.99      | sK3 != X0 ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_1163]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1750,plain,
% 43.44/5.99      ( ~ r1_tarski(sK3,X0)
% 43.44/5.99      | r1_tarski(sK3,k3_subset_1(sK1,sK2))
% 43.44/5.99      | k3_subset_1(sK1,sK2) != X0
% 43.44/5.99      | sK3 != sK3 ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_1672]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2301,plain,
% 43.44/5.99      ( r1_tarski(sK3,k3_subset_1(sK1,sK2))
% 43.44/5.99      | ~ r1_tarski(sK3,k4_xboole_0(sK1,sK2))
% 43.44/5.99      | k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 43.44/5.99      | sK3 != sK3 ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_1750]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_2302,plain,
% 43.44/5.99      ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 43.44/5.99      | sK3 != sK3
% 43.44/5.99      | r1_tarski(sK3,k3_subset_1(sK1,sK2)) = iProver_top
% 43.44/5.99      | r1_tarski(sK3,k4_xboole_0(sK1,sK2)) != iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_2301]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1159,plain,( X0 = X0 ),theory(equality) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1891,plain,
% 43.44/5.99      ( sK3 = sK3 ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_1159]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1164,plain,
% 43.44/5.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 43.44/5.99      theory(equality) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_1170,plain,
% 43.44/5.99      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_1164]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_223,plain,
% 43.44/5.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 43.44/5.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_224,plain,
% 43.44/5.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.44/5.99      inference(renaming,[status(thm)],[c_223]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_563,plain,
% 43.44/5.99      ( r2_hidden(X0,X1)
% 43.44/5.99      | v1_xboole_0(X1)
% 43.44/5.99      | k1_zfmisc_1(sK1) != X1
% 43.44/5.99      | sK3 != X0 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_564,plain,
% 43.44/5.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_563]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_566,plain,
% 43.44/5.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 43.44/5.99      inference(global_propositional_subsumption,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_564,c_42]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_802,plain,
% 43.44/5.99      ( r1_tarski(X0,X1)
% 43.44/5.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 43.44/5.99      | sK3 != X0 ),
% 43.44/5.99      inference(resolution_lifted,[status(thm)],[c_224,c_566]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_803,plain,
% 43.44/5.99      ( r1_tarski(sK3,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 43.44/5.99      inference(unflattening,[status(thm)],[c_802]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_804,plain,
% 43.44/5.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 43.44/5.99      | r1_tarski(sK3,X0) = iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_806,plain,
% 43.44/5.99      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 43.44/5.99      | r1_tarski(sK3,sK1) = iProver_top ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_804]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_646,plain,
% 43.44/5.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
% 43.44/5.99      | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_645]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_3,plain,
% 43.44/5.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 43.44/5.99      inference(cnf_transformation,[],[f48]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_99,plain,
% 43.44/5.99      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_3]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_95,plain,
% 43.44/5.99      ( r1_tarski(sK1,sK1) ),
% 43.44/5.99      inference(instantiation,[status(thm)],[c_5]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_27,negated_conjecture,
% 43.44/5.99      ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
% 43.44/5.99      inference(cnf_transformation,[],[f75]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(c_34,plain,
% 43.44/5.99      ( r1_tarski(sK3,k3_subset_1(sK1,sK2)) != iProver_top ),
% 43.44/5.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 43.44/5.99  
% 43.44/5.99  cnf(contradiction,plain,
% 43.44/5.99      ( $false ),
% 43.44/5.99      inference(minisat,
% 43.44/5.99                [status(thm)],
% 43.44/5.99                [c_75117,c_2302,c_1891,c_1170,c_806,c_646,c_99,c_95,c_34]) ).
% 43.44/5.99  
% 43.44/5.99  
% 43.44/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.44/5.99  
% 43.44/5.99  ------                               Statistics
% 43.44/5.99  
% 43.44/5.99  ------ General
% 43.44/5.99  
% 43.44/5.99  abstr_ref_over_cycles:                  0
% 43.44/5.99  abstr_ref_under_cycles:                 0
% 43.44/5.99  gc_basic_clause_elim:                   0
% 43.44/5.99  forced_gc_time:                         0
% 43.44/5.99  parsing_time:                           0.008
% 43.44/5.99  unif_index_cands_time:                  0.
% 43.44/5.99  unif_index_add_time:                    0.
% 43.44/5.99  orderings_time:                         0.
% 43.44/5.99  out_proof_time:                         0.022
% 43.44/5.99  total_time:                             5.104
% 43.44/5.99  num_of_symbols:                         46
% 43.44/5.99  num_of_terms:                           91712
% 43.44/5.99  
% 43.44/5.99  ------ Preprocessing
% 43.44/5.99  
% 43.44/5.99  num_of_splits:                          0
% 43.44/5.99  num_of_split_atoms:                     0
% 43.44/5.99  num_of_reused_defs:                     0
% 43.44/5.99  num_eq_ax_congr_red:                    20
% 43.44/5.99  num_of_sem_filtered_clauses:            1
% 43.44/5.99  num_of_subtypes:                        0
% 43.44/5.99  monotx_restored_types:                  0
% 43.44/5.99  sat_num_of_epr_types:                   0
% 43.44/5.99  sat_num_of_non_cyclic_types:            0
% 43.44/5.99  sat_guarded_non_collapsed_types:        0
% 43.44/5.99  num_pure_diseq_elim:                    0
% 43.44/5.99  simp_replaced_by:                       0
% 43.44/5.99  res_preprocessed:                       137
% 43.44/5.99  prep_upred:                             0
% 43.44/5.99  prep_unflattend:                        68
% 43.44/5.99  smt_new_axioms:                         0
% 43.44/5.99  pred_elim_cands:                        2
% 43.44/5.99  pred_elim:                              3
% 43.44/5.99  pred_elim_cl:                           0
% 43.44/5.99  pred_elim_cycles:                       6
% 43.44/5.99  merged_defs:                            8
% 43.44/5.99  merged_defs_ncl:                        0
% 43.44/5.99  bin_hyper_res:                          10
% 43.44/5.99  prep_cycles:                            4
% 43.44/5.99  pred_elim_time:                         0.009
% 43.44/5.99  splitting_time:                         0.
% 43.44/5.99  sem_filter_time:                        0.
% 43.44/5.99  monotx_time:                            0.
% 43.44/5.99  subtype_inf_time:                       0.
% 43.44/5.99  
% 43.44/5.99  ------ Problem properties
% 43.44/5.99  
% 43.44/5.99  clauses:                                30
% 43.44/5.99  conjectures:                            2
% 43.44/5.99  epr:                                    4
% 43.44/5.99  horn:                                   29
% 43.44/5.99  ground:                                 4
% 43.44/5.99  unary:                                  12
% 43.44/5.99  binary:                                 13
% 43.44/5.99  lits:                                   53
% 43.44/5.99  lits_eq:                                21
% 43.44/5.99  fd_pure:                                0
% 43.44/5.99  fd_pseudo:                              0
% 43.44/5.99  fd_cond:                                0
% 43.44/5.99  fd_pseudo_cond:                         3
% 43.44/5.99  ac_symbols:                             0
% 43.44/5.99  
% 43.44/5.99  ------ Propositional Solver
% 43.44/5.99  
% 43.44/5.99  prop_solver_calls:                      31
% 43.44/5.99  prop_fast_solver_calls:                 1460
% 43.44/5.99  smt_solver_calls:                       0
% 43.44/5.99  smt_fast_solver_calls:                  0
% 43.44/5.99  prop_num_of_clauses:                    30736
% 43.44/5.99  prop_preprocess_simplified:             39772
% 43.44/5.99  prop_fo_subsumed:                       10
% 43.44/5.99  prop_solver_time:                       0.
% 43.44/5.99  smt_solver_time:                        0.
% 43.44/5.99  smt_fast_solver_time:                   0.
% 43.44/5.99  prop_fast_solver_time:                  0.
% 43.44/5.99  prop_unsat_core_time:                   0.003
% 43.44/5.99  
% 43.44/5.99  ------ QBF
% 43.44/5.99  
% 43.44/5.99  qbf_q_res:                              0
% 43.44/5.99  qbf_num_tautologies:                    0
% 43.44/5.99  qbf_prep_cycles:                        0
% 43.44/5.99  
% 43.44/5.99  ------ BMC1
% 43.44/5.99  
% 43.44/5.99  bmc1_current_bound:                     -1
% 43.44/5.99  bmc1_last_solved_bound:                 -1
% 43.44/5.99  bmc1_unsat_core_size:                   -1
% 43.44/5.99  bmc1_unsat_core_parents_size:           -1
% 43.44/5.99  bmc1_merge_next_fun:                    0
% 43.44/5.99  bmc1_unsat_core_clauses_time:           0.
% 43.44/5.99  
% 43.44/5.99  ------ Instantiation
% 43.44/5.99  
% 43.44/5.99  inst_num_of_clauses:                    5816
% 43.44/5.99  inst_num_in_passive:                    1445
% 43.44/5.99  inst_num_in_active:                     2013
% 43.44/5.99  inst_num_in_unprocessed:                2363
% 43.44/5.99  inst_num_of_loops:                      2290
% 43.44/5.99  inst_num_of_learning_restarts:          0
% 43.44/5.99  inst_num_moves_active_passive:          276
% 43.44/5.99  inst_lit_activity:                      0
% 43.44/5.99  inst_lit_activity_moves:                0
% 43.44/5.99  inst_num_tautologies:                   0
% 43.44/5.99  inst_num_prop_implied:                  0
% 43.44/5.99  inst_num_existing_simplified:           0
% 43.44/5.99  inst_num_eq_res_simplified:             0
% 43.44/5.99  inst_num_child_elim:                    0
% 43.44/5.99  inst_num_of_dismatching_blockings:      8763
% 43.44/5.99  inst_num_of_non_proper_insts:           9800
% 43.44/5.99  inst_num_of_duplicates:                 0
% 43.44/5.99  inst_inst_num_from_inst_to_res:         0
% 43.44/5.99  inst_dismatching_checking_time:         0.
% 43.44/5.99  
% 43.44/5.99  ------ Resolution
% 43.44/5.99  
% 43.44/5.99  res_num_of_clauses:                     0
% 43.44/5.99  res_num_in_passive:                     0
% 43.44/5.99  res_num_in_active:                      0
% 43.44/5.99  res_num_of_loops:                       141
% 43.44/5.99  res_forward_subset_subsumed:            1122
% 43.44/5.99  res_backward_subset_subsumed:           32
% 43.44/5.99  res_forward_subsumed:                   4
% 43.44/5.99  res_backward_subsumed:                  0
% 43.44/5.99  res_forward_subsumption_resolution:     2
% 43.44/5.99  res_backward_subsumption_resolution:    0
% 43.44/5.99  res_clause_to_clause_subsumption:       100397
% 43.44/5.99  res_orphan_elimination:                 0
% 43.44/5.99  res_tautology_del:                      817
% 43.44/5.99  res_num_eq_res_simplified:              0
% 43.44/5.99  res_num_sel_changes:                    0
% 43.44/5.99  res_moves_from_active_to_pass:          0
% 43.44/5.99  
% 43.44/5.99  ------ Superposition
% 43.44/5.99  
% 43.44/5.99  sup_time_total:                         0.
% 43.44/5.99  sup_time_generating:                    0.
% 43.44/5.99  sup_time_sim_full:                      0.
% 43.44/5.99  sup_time_sim_immed:                     0.
% 43.44/5.99  
% 43.44/5.99  sup_num_of_clauses:                     4847
% 43.44/5.99  sup_num_in_active:                      433
% 43.44/5.99  sup_num_in_passive:                     4414
% 43.44/5.99  sup_num_of_loops:                       457
% 43.44/5.99  sup_fw_superposition:                   6774
% 43.44/5.99  sup_bw_superposition:                   4650
% 43.44/5.99  sup_immediate_simplified:               5276
% 43.44/5.99  sup_given_eliminated:                   5
% 43.44/5.99  comparisons_done:                       0
% 43.44/5.99  comparisons_avoided:                    0
% 43.44/5.99  
% 43.44/5.99  ------ Simplifications
% 43.44/5.99  
% 43.44/5.99  
% 43.44/5.99  sim_fw_subset_subsumed:                 20
% 43.44/5.99  sim_bw_subset_subsumed:                 8
% 43.44/5.99  sim_fw_subsumed:                        1115
% 43.44/5.99  sim_bw_subsumed:                        78
% 43.44/5.99  sim_fw_subsumption_res:                 0
% 43.44/5.99  sim_bw_subsumption_res:                 0
% 43.44/5.99  sim_tautology_del:                      272
% 43.44/5.99  sim_eq_tautology_del:                   800
% 43.44/5.99  sim_eq_res_simp:                        0
% 43.44/5.99  sim_fw_demodulated:                     3461
% 43.44/5.99  sim_bw_demodulated:                     256
% 43.44/5.99  sim_light_normalised:                   2791
% 43.44/5.99  sim_joinable_taut:                      0
% 43.44/5.99  sim_joinable_simp:                      0
% 43.44/5.99  sim_ac_normalised:                      0
% 43.44/5.99  sim_smt_subsumption:                    0
% 43.44/5.99  
%------------------------------------------------------------------------------
