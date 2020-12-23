%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:38 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 240 expanded)
%              Number of clauses        :   62 (  92 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :   20
%              Number of atoms          :  304 ( 870 expanded)
%              Number of equality atoms :   93 ( 147 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f34,f33])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
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
    inference(nnf_transformation,[],[f9])).

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

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_534,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_535,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_1654,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_535])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1498,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1842,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1654,c_1498])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1499,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1843,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1654,c_1499])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_543,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_544,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1657,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_544])).

cnf(c_2221,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1843,c_1657])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1790,plain,
    ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1802,plain,
    ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1790])).

cnf(c_1804,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_2225,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2221,c_1804])).

cnf(c_2369,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1842,c_1804,c_2221])).

cnf(c_2373,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2369,c_1657])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1511,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3367,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2373,c_1511])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1514,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3822,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_1514])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1506,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3833,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3822,c_1506])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1504,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7072,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK2,sK3)) = sK1 ),
    inference(superposition,[status(thm)],[c_3833,c_1504])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1509,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1507,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2767,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1507])).

cnf(c_8226,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7072,c_2767])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2213,plain,
    ( r1_tarski(sK2,sK3)
    | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2214,plain,
    ( k4_xboole_0(sK2,sK3) != k1_xboole_0
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_985,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1000,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_990,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_996,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_210,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_211,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_516,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_517,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_519,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_30])).

cnf(c_657,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_519])).

cnf(c_658,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_659,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_661,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8226,c_2225,c_2214,c_1000,c_996,c_661])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.99  
% 3.00/0.99  ------  iProver source info
% 3.00/0.99  
% 3.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.99  git: non_committed_changes: false
% 3.00/0.99  git: last_make_outside_of_git: false
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     num_symb
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       true
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  ------ Parsing...
% 3.00/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.00  ------ Proving...
% 3.00/1.00  ------ Problem Properties 
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  clauses                                 22
% 3.00/1.00  conjectures                             2
% 3.00/1.00  EPR                                     1
% 3.00/1.00  Horn                                    20
% 3.00/1.00  unary                                   2
% 3.00/1.00  binary                                  18
% 3.00/1.00  lits                                    44
% 3.00/1.00  lits eq                                 12
% 3.00/1.00  fd_pure                                 0
% 3.00/1.00  fd_pseudo                               0
% 3.00/1.00  fd_cond                                 1
% 3.00/1.00  fd_pseudo_cond                          2
% 3.00/1.00  AC symbols                              0
% 3.00/1.00  
% 3.00/1.00  ------ Schedule dynamic 5 is on 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  Current options:
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     none
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       false
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ Proving...
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS status Theorem for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  fof(f11,axiom,(
% 3.00/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f22,plain,(
% 3.00/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f11])).
% 3.00/1.00  
% 3.00/1.00  fof(f55,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f22])).
% 3.00/1.00  
% 3.00/1.00  fof(f13,conjecture,(
% 3.00/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f14,negated_conjecture,(
% 3.00/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.00/1.00    inference(negated_conjecture,[],[f13])).
% 3.00/1.00  
% 3.00/1.00  fof(f23,plain,(
% 3.00/1.00    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f14])).
% 3.00/1.00  
% 3.00/1.00  fof(f31,plain,(
% 3.00/1.00    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/1.00    inference(nnf_transformation,[],[f23])).
% 3.00/1.00  
% 3.00/1.00  fof(f32,plain,(
% 3.00/1.00    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/1.00    inference(flattening,[],[f31])).
% 3.00/1.00  
% 3.00/1.00  fof(f34,plain,(
% 3.00/1.00    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f33,plain,(
% 3.00/1.00    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f35,plain,(
% 3.00/1.00    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f34,f33])).
% 3.00/1.00  
% 3.00/1.00  fof(f58,plain,(
% 3.00/1.00    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.00/1.00    inference(cnf_transformation,[],[f35])).
% 3.00/1.00  
% 3.00/1.00  fof(f59,plain,(
% 3.00/1.00    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 3.00/1.00    inference(cnf_transformation,[],[f35])).
% 3.00/1.00  
% 3.00/1.00  fof(f60,plain,(
% 3.00/1.00    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 3.00/1.00    inference(cnf_transformation,[],[f35])).
% 3.00/1.00  
% 3.00/1.00  fof(f57,plain,(
% 3.00/1.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.00/1.00    inference(cnf_transformation,[],[f35])).
% 3.00/1.00  
% 3.00/1.00  fof(f5,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f18,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.00/1.00    inference(ennf_transformation,[],[f5])).
% 3.00/1.00  
% 3.00/1.00  fof(f42,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f18])).
% 3.00/1.00  
% 3.00/1.00  fof(f3,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f16,plain,(
% 3.00/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.00/1.00    inference(ennf_transformation,[],[f3])).
% 3.00/1.00  
% 3.00/1.00  fof(f40,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f16])).
% 3.00/1.00  
% 3.00/1.00  fof(f1,axiom,(
% 3.00/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f15,plain,(
% 3.00/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.00/1.00    inference(ennf_transformation,[],[f1])).
% 3.00/1.00  
% 3.00/1.00  fof(f36,plain,(
% 3.00/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f15])).
% 3.00/1.00  
% 3.00/1.00  fof(f7,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f20,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 3.00/1.00    inference(ennf_transformation,[],[f7])).
% 3.00/1.00  
% 3.00/1.00  fof(f44,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f20])).
% 3.00/1.00  
% 3.00/1.00  fof(f8,axiom,(
% 3.00/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f25,plain,(
% 3.00/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.00/1.00    inference(nnf_transformation,[],[f8])).
% 3.00/1.00  
% 3.00/1.00  fof(f45,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f25])).
% 3.00/1.00  
% 3.00/1.00  fof(f4,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f17,plain,(
% 3.00/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.00/1.00    inference(ennf_transformation,[],[f4])).
% 3.00/1.00  
% 3.00/1.00  fof(f41,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f17])).
% 3.00/1.00  
% 3.00/1.00  fof(f6,axiom,(
% 3.00/1.00    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f19,plain,(
% 3.00/1.00    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f6])).
% 3.00/1.00  
% 3.00/1.00  fof(f43,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f19])).
% 3.00/1.00  
% 3.00/1.00  fof(f2,axiom,(
% 3.00/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f24,plain,(
% 3.00/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.00/1.00    inference(nnf_transformation,[],[f2])).
% 3.00/1.00  
% 3.00/1.00  fof(f37,plain,(
% 3.00/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.00/1.00    inference(cnf_transformation,[],[f24])).
% 3.00/1.00  
% 3.00/1.00  fof(f9,axiom,(
% 3.00/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f26,plain,(
% 3.00/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/1.00    inference(nnf_transformation,[],[f9])).
% 3.00/1.00  
% 3.00/1.00  fof(f27,plain,(
% 3.00/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/1.00    inference(rectify,[],[f26])).
% 3.00/1.00  
% 3.00/1.00  fof(f28,plain,(
% 3.00/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f29,plain,(
% 3.00/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.00/1.00  
% 3.00/1.00  fof(f47,plain,(
% 3.00/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.00/1.00    inference(cnf_transformation,[],[f29])).
% 3.00/1.00  
% 3.00/1.00  fof(f62,plain,(
% 3.00/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.00/1.00    inference(equality_resolution,[],[f47])).
% 3.00/1.00  
% 3.00/1.00  fof(f10,axiom,(
% 3.00/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f21,plain,(
% 3.00/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f10])).
% 3.00/1.00  
% 3.00/1.00  fof(f30,plain,(
% 3.00/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.00/1.00    inference(nnf_transformation,[],[f21])).
% 3.00/1.00  
% 3.00/1.00  fof(f51,plain,(
% 3.00/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f30])).
% 3.00/1.00  
% 3.00/1.00  fof(f12,axiom,(
% 3.00/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f56,plain,(
% 3.00/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f12])).
% 3.00/1.00  
% 3.00/1.00  cnf(c_19,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_23,negated_conjecture,
% 3.00/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_534,plain,
% 3.00/1.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.00/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.00/1.00      | sK3 != X1 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_535,plain,
% 3.00/1.00      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 3.00/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1654,plain,
% 3.00/1.00      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 3.00/1.00      inference(equality_resolution,[status(thm)],[c_535]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_22,negated_conjecture,
% 3.00/1.00      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 3.00/1.00      | r1_tarski(sK2,sK3) ),
% 3.00/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1498,plain,
% 3.00/1.00      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 3.00/1.00      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1842,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 3.00/1.00      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_1654,c_1498]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_21,negated_conjecture,
% 3.00/1.00      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 3.00/1.00      | ~ r1_tarski(sK2,sK3) ),
% 3.00/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1499,plain,
% 3.00/1.00      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 3.00/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1843,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 3.00/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_1654,c_1499]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_24,negated_conjecture,
% 3.00/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_543,plain,
% 3.00/1.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.00/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.00/1.00      | sK2 != X1 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_544,plain,
% 3.00/1.00      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 3.00/1.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_543]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1657,plain,
% 3.00/1.00      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 3.00/1.00      inference(equality_resolution,[status(thm)],[c_544]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2221,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 3.00/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_1843,c_1657]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6,plain,
% 3.00/1.00      ( ~ r1_tarski(X0,X1)
% 3.00/1.00      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1790,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2))
% 3.00/1.00      | ~ r1_tarski(sK2,sK3) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1802,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(X0,sK3),k4_xboole_0(X0,sK2)) = iProver_top
% 3.00/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1790]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1804,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 3.00/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_1802]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2225,plain,
% 3.00/1.00      ( r1_tarski(sK2,sK3) != iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_2221,c_1804]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2369,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_1842,c_1804,c_2221]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2373,plain,
% 3.00/1.00      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_2369,c_1657]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3,plain,
% 3.00/1.00      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 3.00/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1511,plain,
% 3.00/1.00      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 3.00/1.00      | r1_xboole_0(X0,X2) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3367,plain,
% 3.00/1.00      ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_2373,c_1511]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_0,plain,
% 3.00/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1514,plain,
% 3.00/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.00/1.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3822,plain,
% 3.00/1.00      ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3367,c_1514]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_8,plain,
% 3.00/1.00      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 3.00/1.00      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1506,plain,
% 3.00/1.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) != iProver_top
% 3.00/1.00      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3833,plain,
% 3.00/1.00      ( r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3822,c_1506]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_10,plain,
% 3.00/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1504,plain,
% 3.00/1.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7072,plain,
% 3.00/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK2,sK3)) = sK1 ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_3833,c_1504]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_5,plain,
% 3.00/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1509,plain,
% 3.00/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.00/1.00      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7,plain,
% 3.00/1.00      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1507,plain,
% 3.00/1.00      ( k1_xboole_0 = X0
% 3.00/1.00      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2767,plain,
% 3.00/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.00/1.00      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_1509,c_1507]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_8226,plain,
% 3.00/1.00      ( k4_xboole_0(sK2,sK3) = k1_xboole_0
% 3.00/1.00      | r1_tarski(sK2,sK1) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_7072,c_2767]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2,plain,
% 3.00/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2213,plain,
% 3.00/1.00      ( r1_tarski(sK2,sK3) | k4_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2214,plain,
% 3.00/1.00      ( k4_xboole_0(sK2,sK3) != k1_xboole_0
% 3.00/1.00      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_985,plain,( X0 = X0 ),theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1000,plain,
% 3.00/1.00      ( sK1 = sK1 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_985]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_990,plain,
% 3.00/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.00/1.00      theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_996,plain,
% 3.00/1.00      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_990]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_14,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_210,plain,
% 3.00/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.00/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_211,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_210]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_18,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_516,plain,
% 3.00/1.00      ( r2_hidden(X0,X1)
% 3.00/1.00      | v1_xboole_0(X1)
% 3.00/1.00      | k1_zfmisc_1(sK1) != X1
% 3.00/1.00      | sK2 != X0 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_517,plain,
% 3.00/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_20,plain,
% 3.00/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_30,plain,
% 3.00/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_519,plain,
% 3.00/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_517,c_30]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_657,plain,
% 3.00/1.00      ( r1_tarski(X0,X1)
% 3.00/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 3.00/1.00      | sK2 != X0 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_211,c_519]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_658,plain,
% 3.00/1.00      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_657]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_659,plain,
% 3.00/1.00      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.00/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_661,plain,
% 3.00/1.00      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 3.00/1.00      | r1_tarski(sK2,sK1) = iProver_top ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_659]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(contradiction,plain,
% 3.00/1.00      ( $false ),
% 3.00/1.00      inference(minisat,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_8226,c_2225,c_2214,c_1000,c_996,c_661]) ).
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  ------                               Statistics
% 3.00/1.00  
% 3.00/1.00  ------ General
% 3.00/1.00  
% 3.00/1.00  abstr_ref_over_cycles:                  0
% 3.00/1.00  abstr_ref_under_cycles:                 0
% 3.00/1.00  gc_basic_clause_elim:                   0
% 3.00/1.00  forced_gc_time:                         0
% 3.00/1.00  parsing_time:                           0.025
% 3.00/1.00  unif_index_cands_time:                  0.
% 3.00/1.00  unif_index_add_time:                    0.
% 3.00/1.00  orderings_time:                         0.
% 3.00/1.00  out_proof_time:                         0.013
% 3.00/1.00  total_time:                             0.276
% 3.00/1.00  num_of_symbols:                         44
% 3.00/1.00  num_of_terms:                           8790
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing
% 3.00/1.00  
% 3.00/1.00  num_of_splits:                          0
% 3.00/1.00  num_of_split_atoms:                     0
% 3.00/1.00  num_of_reused_defs:                     0
% 3.00/1.00  num_eq_ax_congr_red:                    13
% 3.00/1.00  num_of_sem_filtered_clauses:            1
% 3.00/1.00  num_of_subtypes:                        0
% 3.00/1.00  monotx_restored_types:                  0
% 3.00/1.00  sat_num_of_epr_types:                   0
% 3.00/1.00  sat_num_of_non_cyclic_types:            0
% 3.00/1.00  sat_guarded_non_collapsed_types:        0
% 3.00/1.00  num_pure_diseq_elim:                    0
% 3.00/1.00  simp_replaced_by:                       0
% 3.00/1.00  res_preprocessed:                       108
% 3.00/1.00  prep_upred:                             0
% 3.00/1.00  prep_unflattend:                        46
% 3.00/1.00  smt_new_axioms:                         0
% 3.00/1.00  pred_elim_cands:                        3
% 3.00/1.00  pred_elim:                              2
% 3.00/1.00  pred_elim_cl:                           3
% 3.00/1.00  pred_elim_cycles:                       5
% 3.00/1.00  merged_defs:                            32
% 3.00/1.00  merged_defs_ncl:                        0
% 3.00/1.00  bin_hyper_res:                          33
% 3.00/1.00  prep_cycles:                            4
% 3.00/1.00  pred_elim_time:                         0.008
% 3.00/1.00  splitting_time:                         0.
% 3.00/1.00  sem_filter_time:                        0.
% 3.00/1.00  monotx_time:                            0.001
% 3.00/1.00  subtype_inf_time:                       0.
% 3.00/1.00  
% 3.00/1.00  ------ Problem properties
% 3.00/1.00  
% 3.00/1.00  clauses:                                22
% 3.00/1.00  conjectures:                            2
% 3.00/1.00  epr:                                    1
% 3.00/1.00  horn:                                   20
% 3.00/1.00  ground:                                 4
% 3.00/1.00  unary:                                  2
% 3.00/1.00  binary:                                 18
% 3.00/1.00  lits:                                   44
% 3.00/1.00  lits_eq:                                12
% 3.00/1.00  fd_pure:                                0
% 3.00/1.00  fd_pseudo:                              0
% 3.00/1.00  fd_cond:                                1
% 3.00/1.00  fd_pseudo_cond:                         2
% 3.00/1.00  ac_symbols:                             0
% 3.00/1.00  
% 3.00/1.00  ------ Propositional Solver
% 3.00/1.00  
% 3.00/1.00  prop_solver_calls:                      27
% 3.00/1.00  prop_fast_solver_calls:                 672
% 3.00/1.00  smt_solver_calls:                       0
% 3.00/1.00  smt_fast_solver_calls:                  0
% 3.00/1.00  prop_num_of_clauses:                    3637
% 3.00/1.00  prop_preprocess_simplified:             8118
% 3.00/1.00  prop_fo_subsumed:                       7
% 3.00/1.00  prop_solver_time:                       0.
% 3.00/1.00  smt_solver_time:                        0.
% 3.00/1.00  smt_fast_solver_time:                   0.
% 3.00/1.00  prop_fast_solver_time:                  0.
% 3.00/1.00  prop_unsat_core_time:                   0.
% 3.00/1.00  
% 3.00/1.00  ------ QBF
% 3.00/1.00  
% 3.00/1.00  qbf_q_res:                              0
% 3.00/1.00  qbf_num_tautologies:                    0
% 3.00/1.00  qbf_prep_cycles:                        0
% 3.00/1.00  
% 3.00/1.00  ------ BMC1
% 3.00/1.00  
% 3.00/1.00  bmc1_current_bound:                     -1
% 3.00/1.00  bmc1_last_solved_bound:                 -1
% 3.00/1.00  bmc1_unsat_core_size:                   -1
% 3.00/1.00  bmc1_unsat_core_parents_size:           -1
% 3.00/1.00  bmc1_merge_next_fun:                    0
% 3.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation
% 3.00/1.00  
% 3.00/1.00  inst_num_of_clauses:                    983
% 3.00/1.00  inst_num_in_passive:                    181
% 3.00/1.00  inst_num_in_active:                     354
% 3.00/1.00  inst_num_in_unprocessed:                448
% 3.00/1.00  inst_num_of_loops:                      430
% 3.00/1.00  inst_num_of_learning_restarts:          0
% 3.00/1.00  inst_num_moves_active_passive:          75
% 3.00/1.00  inst_lit_activity:                      0
% 3.00/1.00  inst_lit_activity_moves:                0
% 3.00/1.00  inst_num_tautologies:                   0
% 3.00/1.00  inst_num_prop_implied:                  0
% 3.00/1.00  inst_num_existing_simplified:           0
% 3.00/1.00  inst_num_eq_res_simplified:             0
% 3.00/1.00  inst_num_child_elim:                    0
% 3.00/1.00  inst_num_of_dismatching_blockings:      383
% 3.00/1.00  inst_num_of_non_proper_insts:           732
% 3.00/1.00  inst_num_of_duplicates:                 0
% 3.00/1.00  inst_inst_num_from_inst_to_res:         0
% 3.00/1.00  inst_dismatching_checking_time:         0.
% 3.00/1.00  
% 3.00/1.00  ------ Resolution
% 3.00/1.00  
% 3.00/1.00  res_num_of_clauses:                     0
% 3.00/1.00  res_num_in_passive:                     0
% 3.00/1.00  res_num_in_active:                      0
% 3.00/1.00  res_num_of_loops:                       112
% 3.00/1.00  res_forward_subset_subsumed:            30
% 3.00/1.00  res_backward_subset_subsumed:           0
% 3.00/1.00  res_forward_subsumed:                   3
% 3.00/1.00  res_backward_subsumed:                  0
% 3.00/1.00  res_forward_subsumption_resolution:     2
% 3.00/1.00  res_backward_subsumption_resolution:    0
% 3.00/1.00  res_clause_to_clause_subsumption:       539
% 3.00/1.00  res_orphan_elimination:                 0
% 3.00/1.00  res_tautology_del:                      153
% 3.00/1.00  res_num_eq_res_simplified:              0
% 3.00/1.00  res_num_sel_changes:                    0
% 3.00/1.00  res_moves_from_active_to_pass:          0
% 3.00/1.00  
% 3.00/1.00  ------ Superposition
% 3.00/1.00  
% 3.00/1.00  sup_time_total:                         0.
% 3.00/1.00  sup_time_generating:                    0.
% 3.00/1.00  sup_time_sim_full:                      0.
% 3.00/1.00  sup_time_sim_immed:                     0.
% 3.00/1.00  
% 3.00/1.00  sup_num_of_clauses:                     228
% 3.00/1.00  sup_num_in_active:                      83
% 3.00/1.00  sup_num_in_passive:                     145
% 3.00/1.00  sup_num_of_loops:                       84
% 3.00/1.00  sup_fw_superposition:                   118
% 3.00/1.00  sup_bw_superposition:                   223
% 3.00/1.00  sup_immediate_simplified:               20
% 3.00/1.00  sup_given_eliminated:                   0
% 3.00/1.00  comparisons_done:                       0
% 3.00/1.00  comparisons_avoided:                    0
% 3.00/1.00  
% 3.00/1.00  ------ Simplifications
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  sim_fw_subset_subsumed:                 20
% 3.00/1.00  sim_bw_subset_subsumed:                 1
% 3.00/1.00  sim_fw_subsumed:                        0
% 3.00/1.00  sim_bw_subsumed:                        0
% 3.00/1.00  sim_fw_subsumption_res:                 0
% 3.00/1.00  sim_bw_subsumption_res:                 0
% 3.00/1.00  sim_tautology_del:                      21
% 3.00/1.00  sim_eq_tautology_del:                   10
% 3.00/1.00  sim_eq_res_simp:                        0
% 3.00/1.00  sim_fw_demodulated:                     5
% 3.00/1.00  sim_bw_demodulated:                     2
% 3.00/1.00  sim_light_normalised:                   16
% 3.00/1.00  sim_joinable_taut:                      0
% 3.00/1.00  sim_joinable_simp:                      0
% 3.00/1.00  sim_ac_normalised:                      0
% 3.00/1.00  sim_smt_subsumption:                    0
% 3.00/1.00  
%------------------------------------------------------------------------------
