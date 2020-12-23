%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:40 EST 2020

% Result     : Theorem 39.63s
% Output     : CNFRefutation 39.63s
% Verified   : 
% Statistics : Number of formulae       :  216 (8415 expanded)
%              Number of clauses        :  145 (2860 expanded)
%              Number of leaves         :   21 (2345 expanded)
%              Depth                    :   37
%              Number of atoms          :  415 (10122 expanded)
%              Number of equality atoms :  198 (8197 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f44,f58,f58])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f15,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(X1,sK3)
          | ~ r1_xboole_0(X1,k3_subset_1(X0,sK3)) )
        & ( r1_tarski(X1,sK3)
          | r1_xboole_0(X1,k3_subset_1(X0,sK3)) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK2,X2)
            | ~ r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
          & ( r1_tarski(sK2,X2)
            | r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ r1_tarski(sK2,sK3)
      | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
    & ( r1_tarski(sK2,sK3)
      | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f41,f40])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,
    ( r1_tarski(sK2,sK3)
    | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3477,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_14])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3285,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_13,c_2])).

cnf(c_3748,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[status(thm)],[c_3477,c_3285])).

cnf(c_3754,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_3748,c_3477])).

cnf(c_6132,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_3754,c_2])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3751,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3477,c_5])).

cnf(c_3757,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_3754,c_3751])).

cnf(c_6144,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_6132,c_3757])).

cnf(c_6145,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_6144,c_5,c_3477])).

cnf(c_17,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1775,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2909,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1775])).

cnf(c_3624,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3285,c_2909])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1783,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13624,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3624,c_1783])).

cnf(c_3614,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3285,c_14])).

cnf(c_3622,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3285,c_1775])).

cnf(c_4074,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3285,c_3622])).

cnf(c_7301,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_4074])).

cnf(c_7312,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3614,c_5])).

cnf(c_7334,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_7312,c_14])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3476,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_14])).

cnf(c_5092,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_3476])).

cnf(c_7335,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_7334,c_5092])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3618,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3285,c_0])).

cnf(c_7306,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_3614,c_3618])).

cnf(c_7342,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_7306,c_7335])).

cnf(c_7343,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7342,c_3618])).

cnf(c_7354,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7301,c_7335,c_7343])).

cnf(c_13633,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7354,c_1783])).

cnf(c_3621,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3285,c_14])).

cnf(c_8573,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_2,c_3621])).

cnf(c_8577,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_3285,c_3621])).

cnf(c_8726,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_8577,c_7343])).

cnf(c_8727,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_8726,c_14])).

cnf(c_8730,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),X1) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_8573,c_8727])).

cnf(c_8731,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_8730,c_13,c_7343])).

cnf(c_13687,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13633,c_8731])).

cnf(c_3626,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_3285,c_5])).

cnf(c_12328,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_8731,c_3626])).

cnf(c_7663,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3285,c_7343])).

cnf(c_12336,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_12328,c_7663])).

cnf(c_13688,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13687,c_12336])).

cnf(c_13714,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13624,c_13688])).

cnf(c_13715,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13714,c_13])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_669,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_670,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_676,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_670,c_27])).

cnf(c_1768,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1771,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3281,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1771])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1778,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8060,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_3281,c_1778])).

cnf(c_8805,plain,
    ( k5_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_8060,c_0])).

cnf(c_2798,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_8812,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_8805,c_2798])).

cnf(c_13782,plain,
    ( k4_xboole_0(sK3,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13715,c_8812])).

cnf(c_3474,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_2,c_14])).

cnf(c_40285,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_13782,c_3474])).

cnf(c_40496,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_40285,c_14,c_6145])).

cnf(c_40996,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK3),X0),X1)) = k4_xboole_0(k4_xboole_0(sK3,X0),X1) ),
    inference(superposition,[status(thm)],[c_40496,c_14])).

cnf(c_3478,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_14,c_14])).

cnf(c_3495,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_3478,c_14])).

cnf(c_41032,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK3),X0),X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_40996,c_14,c_3495])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_682,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_683,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_689,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_683,c_27])).

cnf(c_1767,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_3282,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_1771])).

cnf(c_8061,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_3282,c_1778])).

cnf(c_8960,plain,
    ( k5_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_8061,c_0])).

cnf(c_8967,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_8960,c_2798])).

cnf(c_13770,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13715,c_8967])).

cnf(c_40286,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_13770,c_3474])).

cnf(c_40495,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_40286,c_14,c_6145])).

cnf(c_40668,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1,c_40495])).

cnf(c_117026,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(superposition,[status(thm)],[c_41032,c_40668])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK2,sK3)
    | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1769,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_695,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_696,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_1902,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_696])).

cnf(c_2057,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1769,c_1902])).

cnf(c_13617,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_1783])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1776,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7099,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6145,c_1776])).

cnf(c_100400,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13617,c_7099])).

cnf(c_2445,plain,
    ( ~ r1_xboole_0(X0,k4_xboole_0(sK1,sK3))
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2447,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2445])).

cnf(c_13736,plain,
    ( r1_tarski(sK2,sK3)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13617])).

cnf(c_6168,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_6145])).

cnf(c_40985,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6168,c_40496])).

cnf(c_41037,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_40985,c_13])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1780,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_42215,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_41037,c_1780])).

cnf(c_42241,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_42215])).

cnf(c_42243,plain,
    ( ~ r1_tarski(sK2,sK3)
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_42241])).

cnf(c_101292,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_100400,c_2447,c_13736,c_42243])).

cnf(c_101466,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_101292,c_0])).

cnf(c_3290,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1775])).

cnf(c_8959,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8061,c_3290])).

cnf(c_13643,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8959,c_1783])).

cnf(c_17900,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13643,c_0])).

cnf(c_2800,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_2801,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2800,c_13])).

cnf(c_13761,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_13715,c_2801])).

cnf(c_17910,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_17900,c_13761])).

cnf(c_17922,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_17900,c_17910])).

cnf(c_101533,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_101466,c_17922])).

cnf(c_102382,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_101533,c_14])).

cnf(c_117046,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_117026,c_102382])).

cnf(c_133525,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6145,c_117046])).

cnf(c_42279,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_40668,c_40496])).

cnf(c_133653,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_133525,c_13,c_42279])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1779,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_134852,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_133653,c_1779])).

cnf(c_134942,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_134852])).

cnf(c_28,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1770,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2054,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1770,c_1902])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1967,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK1,sK3))
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1968,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) != k1_xboole_0
    | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1967])).

cnf(c_1970,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) != k1_xboole_0
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_85,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_87,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_134942,c_101292,c_2054,c_1970,c_87])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.63/5.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.63/5.52  
% 39.63/5.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.63/5.52  
% 39.63/5.52  ------  iProver source info
% 39.63/5.52  
% 39.63/5.52  git: date: 2020-06-30 10:37:57 +0100
% 39.63/5.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.63/5.52  git: non_committed_changes: false
% 39.63/5.52  git: last_make_outside_of_git: false
% 39.63/5.52  
% 39.63/5.52  ------ 
% 39.63/5.52  
% 39.63/5.52  ------ Input Options
% 39.63/5.52  
% 39.63/5.52  --out_options                           all
% 39.63/5.52  --tptp_safe_out                         true
% 39.63/5.52  --problem_path                          ""
% 39.63/5.52  --include_path                          ""
% 39.63/5.52  --clausifier                            res/vclausify_rel
% 39.63/5.52  --clausifier_options                    ""
% 39.63/5.52  --stdin                                 false
% 39.63/5.52  --stats_out                             all
% 39.63/5.52  
% 39.63/5.52  ------ General Options
% 39.63/5.52  
% 39.63/5.52  --fof                                   false
% 39.63/5.52  --time_out_real                         305.
% 39.63/5.52  --time_out_virtual                      -1.
% 39.63/5.52  --symbol_type_check                     false
% 39.63/5.52  --clausify_out                          false
% 39.63/5.52  --sig_cnt_out                           false
% 39.63/5.52  --trig_cnt_out                          false
% 39.63/5.52  --trig_cnt_out_tolerance                1.
% 39.63/5.52  --trig_cnt_out_sk_spl                   false
% 39.63/5.52  --abstr_cl_out                          false
% 39.63/5.52  
% 39.63/5.52  ------ Global Options
% 39.63/5.52  
% 39.63/5.52  --schedule                              default
% 39.63/5.52  --add_important_lit                     false
% 39.63/5.52  --prop_solver_per_cl                    1000
% 39.63/5.52  --min_unsat_core                        false
% 39.63/5.52  --soft_assumptions                      false
% 39.63/5.52  --soft_lemma_size                       3
% 39.63/5.52  --prop_impl_unit_size                   0
% 39.63/5.52  --prop_impl_unit                        []
% 39.63/5.52  --share_sel_clauses                     true
% 39.63/5.52  --reset_solvers                         false
% 39.63/5.52  --bc_imp_inh                            [conj_cone]
% 39.63/5.52  --conj_cone_tolerance                   3.
% 39.63/5.52  --extra_neg_conj                        none
% 39.63/5.52  --large_theory_mode                     true
% 39.63/5.52  --prolific_symb_bound                   200
% 39.63/5.52  --lt_threshold                          2000
% 39.63/5.52  --clause_weak_htbl                      true
% 39.63/5.52  --gc_record_bc_elim                     false
% 39.63/5.52  
% 39.63/5.52  ------ Preprocessing Options
% 39.63/5.52  
% 39.63/5.52  --preprocessing_flag                    true
% 39.63/5.52  --time_out_prep_mult                    0.1
% 39.63/5.52  --splitting_mode                        input
% 39.63/5.52  --splitting_grd                         true
% 39.63/5.52  --splitting_cvd                         false
% 39.63/5.52  --splitting_cvd_svl                     false
% 39.63/5.52  --splitting_nvd                         32
% 39.63/5.52  --sub_typing                            true
% 39.63/5.52  --prep_gs_sim                           true
% 39.63/5.52  --prep_unflatten                        true
% 39.63/5.52  --prep_res_sim                          true
% 39.63/5.52  --prep_upred                            true
% 39.63/5.52  --prep_sem_filter                       exhaustive
% 39.63/5.52  --prep_sem_filter_out                   false
% 39.63/5.52  --pred_elim                             true
% 39.63/5.52  --res_sim_input                         true
% 39.63/5.52  --eq_ax_congr_red                       true
% 39.63/5.52  --pure_diseq_elim                       true
% 39.63/5.52  --brand_transform                       false
% 39.63/5.52  --non_eq_to_eq                          false
% 39.63/5.52  --prep_def_merge                        true
% 39.63/5.52  --prep_def_merge_prop_impl              false
% 39.63/5.52  --prep_def_merge_mbd                    true
% 39.63/5.52  --prep_def_merge_tr_red                 false
% 39.63/5.52  --prep_def_merge_tr_cl                  false
% 39.63/5.52  --smt_preprocessing                     true
% 39.63/5.52  --smt_ac_axioms                         fast
% 39.63/5.52  --preprocessed_out                      false
% 39.63/5.52  --preprocessed_stats                    false
% 39.63/5.52  
% 39.63/5.52  ------ Abstraction refinement Options
% 39.63/5.52  
% 39.63/5.52  --abstr_ref                             []
% 39.63/5.52  --abstr_ref_prep                        false
% 39.63/5.52  --abstr_ref_until_sat                   false
% 39.63/5.52  --abstr_ref_sig_restrict                funpre
% 39.63/5.52  --abstr_ref_af_restrict_to_split_sk     false
% 39.63/5.52  --abstr_ref_under                       []
% 39.63/5.52  
% 39.63/5.52  ------ SAT Options
% 39.63/5.52  
% 39.63/5.52  --sat_mode                              false
% 39.63/5.52  --sat_fm_restart_options                ""
% 39.63/5.52  --sat_gr_def                            false
% 39.63/5.52  --sat_epr_types                         true
% 39.63/5.52  --sat_non_cyclic_types                  false
% 39.63/5.52  --sat_finite_models                     false
% 39.63/5.52  --sat_fm_lemmas                         false
% 39.63/5.52  --sat_fm_prep                           false
% 39.63/5.52  --sat_fm_uc_incr                        true
% 39.63/5.52  --sat_out_model                         small
% 39.63/5.52  --sat_out_clauses                       false
% 39.63/5.52  
% 39.63/5.52  ------ QBF Options
% 39.63/5.52  
% 39.63/5.52  --qbf_mode                              false
% 39.63/5.52  --qbf_elim_univ                         false
% 39.63/5.52  --qbf_dom_inst                          none
% 39.63/5.52  --qbf_dom_pre_inst                      false
% 39.63/5.52  --qbf_sk_in                             false
% 39.63/5.52  --qbf_pred_elim                         true
% 39.63/5.52  --qbf_split                             512
% 39.63/5.52  
% 39.63/5.52  ------ BMC1 Options
% 39.63/5.52  
% 39.63/5.52  --bmc1_incremental                      false
% 39.63/5.52  --bmc1_axioms                           reachable_all
% 39.63/5.52  --bmc1_min_bound                        0
% 39.63/5.52  --bmc1_max_bound                        -1
% 39.63/5.52  --bmc1_max_bound_default                -1
% 39.63/5.52  --bmc1_symbol_reachability              true
% 39.63/5.52  --bmc1_property_lemmas                  false
% 39.63/5.52  --bmc1_k_induction                      false
% 39.63/5.52  --bmc1_non_equiv_states                 false
% 39.63/5.52  --bmc1_deadlock                         false
% 39.63/5.52  --bmc1_ucm                              false
% 39.63/5.52  --bmc1_add_unsat_core                   none
% 39.63/5.52  --bmc1_unsat_core_children              false
% 39.63/5.52  --bmc1_unsat_core_extrapolate_axioms    false
% 39.63/5.52  --bmc1_out_stat                         full
% 39.63/5.52  --bmc1_ground_init                      false
% 39.63/5.52  --bmc1_pre_inst_next_state              false
% 39.63/5.52  --bmc1_pre_inst_state                   false
% 39.63/5.52  --bmc1_pre_inst_reach_state             false
% 39.63/5.52  --bmc1_out_unsat_core                   false
% 39.63/5.52  --bmc1_aig_witness_out                  false
% 39.63/5.52  --bmc1_verbose                          false
% 39.63/5.52  --bmc1_dump_clauses_tptp                false
% 39.63/5.52  --bmc1_dump_unsat_core_tptp             false
% 39.63/5.52  --bmc1_dump_file                        -
% 39.63/5.52  --bmc1_ucm_expand_uc_limit              128
% 39.63/5.52  --bmc1_ucm_n_expand_iterations          6
% 39.63/5.52  --bmc1_ucm_extend_mode                  1
% 39.63/5.52  --bmc1_ucm_init_mode                    2
% 39.63/5.52  --bmc1_ucm_cone_mode                    none
% 39.63/5.52  --bmc1_ucm_reduced_relation_type        0
% 39.63/5.52  --bmc1_ucm_relax_model                  4
% 39.63/5.52  --bmc1_ucm_full_tr_after_sat            true
% 39.63/5.52  --bmc1_ucm_expand_neg_assumptions       false
% 39.63/5.52  --bmc1_ucm_layered_model                none
% 39.63/5.52  --bmc1_ucm_max_lemma_size               10
% 39.63/5.52  
% 39.63/5.52  ------ AIG Options
% 39.63/5.52  
% 39.63/5.52  --aig_mode                              false
% 39.63/5.52  
% 39.63/5.52  ------ Instantiation Options
% 39.63/5.52  
% 39.63/5.52  --instantiation_flag                    true
% 39.63/5.52  --inst_sos_flag                         true
% 39.63/5.52  --inst_sos_phase                        true
% 39.63/5.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.63/5.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.63/5.52  --inst_lit_sel_side                     num_symb
% 39.63/5.52  --inst_solver_per_active                1400
% 39.63/5.52  --inst_solver_calls_frac                1.
% 39.63/5.52  --inst_passive_queue_type               priority_queues
% 39.63/5.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.63/5.52  --inst_passive_queues_freq              [25;2]
% 39.63/5.52  --inst_dismatching                      true
% 39.63/5.52  --inst_eager_unprocessed_to_passive     true
% 39.63/5.52  --inst_prop_sim_given                   true
% 39.63/5.52  --inst_prop_sim_new                     false
% 39.63/5.52  --inst_subs_new                         false
% 39.63/5.52  --inst_eq_res_simp                      false
% 39.63/5.52  --inst_subs_given                       false
% 39.63/5.52  --inst_orphan_elimination               true
% 39.63/5.52  --inst_learning_loop_flag               true
% 39.63/5.52  --inst_learning_start                   3000
% 39.63/5.52  --inst_learning_factor                  2
% 39.63/5.52  --inst_start_prop_sim_after_learn       3
% 39.63/5.52  --inst_sel_renew                        solver
% 39.63/5.52  --inst_lit_activity_flag                true
% 39.63/5.52  --inst_restr_to_given                   false
% 39.63/5.52  --inst_activity_threshold               500
% 39.63/5.52  --inst_out_proof                        true
% 39.63/5.52  
% 39.63/5.52  ------ Resolution Options
% 39.63/5.52  
% 39.63/5.52  --resolution_flag                       true
% 39.63/5.52  --res_lit_sel                           adaptive
% 39.63/5.52  --res_lit_sel_side                      none
% 39.63/5.52  --res_ordering                          kbo
% 39.63/5.52  --res_to_prop_solver                    active
% 39.63/5.52  --res_prop_simpl_new                    false
% 39.63/5.52  --res_prop_simpl_given                  true
% 39.63/5.52  --res_passive_queue_type                priority_queues
% 39.63/5.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.63/5.52  --res_passive_queues_freq               [15;5]
% 39.63/5.52  --res_forward_subs                      full
% 39.63/5.52  --res_backward_subs                     full
% 39.63/5.52  --res_forward_subs_resolution           true
% 39.63/5.52  --res_backward_subs_resolution          true
% 39.63/5.52  --res_orphan_elimination                true
% 39.63/5.52  --res_time_limit                        2.
% 39.63/5.52  --res_out_proof                         true
% 39.63/5.52  
% 39.63/5.52  ------ Superposition Options
% 39.63/5.52  
% 39.63/5.52  --superposition_flag                    true
% 39.63/5.52  --sup_passive_queue_type                priority_queues
% 39.63/5.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.63/5.52  --sup_passive_queues_freq               [8;1;4]
% 39.63/5.52  --demod_completeness_check              fast
% 39.63/5.52  --demod_use_ground                      true
% 39.63/5.52  --sup_to_prop_solver                    passive
% 39.63/5.52  --sup_prop_simpl_new                    true
% 39.63/5.52  --sup_prop_simpl_given                  true
% 39.63/5.52  --sup_fun_splitting                     true
% 39.63/5.52  --sup_smt_interval                      50000
% 39.63/5.52  
% 39.63/5.52  ------ Superposition Simplification Setup
% 39.63/5.52  
% 39.63/5.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.63/5.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.63/5.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.63/5.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.63/5.52  --sup_full_triv                         [TrivRules;PropSubs]
% 39.63/5.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.63/5.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.63/5.52  --sup_immed_triv                        [TrivRules]
% 39.63/5.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.63/5.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.63/5.52  --sup_immed_bw_main                     []
% 39.63/5.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.63/5.52  --sup_input_triv                        [Unflattening;TrivRules]
% 39.63/5.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.63/5.52  --sup_input_bw                          []
% 39.63/5.52  
% 39.63/5.52  ------ Combination Options
% 39.63/5.52  
% 39.63/5.52  --comb_res_mult                         3
% 39.63/5.52  --comb_sup_mult                         2
% 39.63/5.52  --comb_inst_mult                        10
% 39.63/5.52  
% 39.63/5.52  ------ Debug Options
% 39.63/5.52  
% 39.63/5.52  --dbg_backtrace                         false
% 39.63/5.52  --dbg_dump_prop_clauses                 false
% 39.63/5.52  --dbg_dump_prop_clauses_file            -
% 39.63/5.52  --dbg_out_stat                          false
% 39.63/5.52  ------ Parsing...
% 39.63/5.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.63/5.52  
% 39.63/5.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 39.63/5.52  
% 39.63/5.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.63/5.52  
% 39.63/5.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.63/5.52  ------ Proving...
% 39.63/5.52  ------ Problem Properties 
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  clauses                                 28
% 39.63/5.52  conjectures                             2
% 39.63/5.52  EPR                                     3
% 39.63/5.52  Horn                                    26
% 39.63/5.52  unary                                   12
% 39.63/5.52  binary                                  12
% 39.63/5.52  lits                                    48
% 39.63/5.52  lits eq                                 18
% 39.63/5.52  fd_pure                                 0
% 39.63/5.52  fd_pseudo                               0
% 39.63/5.52  fd_cond                                 0
% 39.63/5.52  fd_pseudo_cond                          3
% 39.63/5.52  AC symbols                              0
% 39.63/5.52  
% 39.63/5.52  ------ Schedule dynamic 5 is on 
% 39.63/5.52  
% 39.63/5.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  ------ 
% 39.63/5.52  Current options:
% 39.63/5.52  ------ 
% 39.63/5.52  
% 39.63/5.52  ------ Input Options
% 39.63/5.52  
% 39.63/5.52  --out_options                           all
% 39.63/5.52  --tptp_safe_out                         true
% 39.63/5.52  --problem_path                          ""
% 39.63/5.52  --include_path                          ""
% 39.63/5.52  --clausifier                            res/vclausify_rel
% 39.63/5.52  --clausifier_options                    ""
% 39.63/5.52  --stdin                                 false
% 39.63/5.52  --stats_out                             all
% 39.63/5.52  
% 39.63/5.52  ------ General Options
% 39.63/5.52  
% 39.63/5.52  --fof                                   false
% 39.63/5.52  --time_out_real                         305.
% 39.63/5.52  --time_out_virtual                      -1.
% 39.63/5.52  --symbol_type_check                     false
% 39.63/5.52  --clausify_out                          false
% 39.63/5.52  --sig_cnt_out                           false
% 39.63/5.52  --trig_cnt_out                          false
% 39.63/5.52  --trig_cnt_out_tolerance                1.
% 39.63/5.52  --trig_cnt_out_sk_spl                   false
% 39.63/5.52  --abstr_cl_out                          false
% 39.63/5.52  
% 39.63/5.52  ------ Global Options
% 39.63/5.52  
% 39.63/5.52  --schedule                              default
% 39.63/5.52  --add_important_lit                     false
% 39.63/5.52  --prop_solver_per_cl                    1000
% 39.63/5.52  --min_unsat_core                        false
% 39.63/5.52  --soft_assumptions                      false
% 39.63/5.52  --soft_lemma_size                       3
% 39.63/5.52  --prop_impl_unit_size                   0
% 39.63/5.52  --prop_impl_unit                        []
% 39.63/5.52  --share_sel_clauses                     true
% 39.63/5.52  --reset_solvers                         false
% 39.63/5.52  --bc_imp_inh                            [conj_cone]
% 39.63/5.52  --conj_cone_tolerance                   3.
% 39.63/5.52  --extra_neg_conj                        none
% 39.63/5.52  --large_theory_mode                     true
% 39.63/5.52  --prolific_symb_bound                   200
% 39.63/5.52  --lt_threshold                          2000
% 39.63/5.52  --clause_weak_htbl                      true
% 39.63/5.52  --gc_record_bc_elim                     false
% 39.63/5.52  
% 39.63/5.52  ------ Preprocessing Options
% 39.63/5.52  
% 39.63/5.52  --preprocessing_flag                    true
% 39.63/5.52  --time_out_prep_mult                    0.1
% 39.63/5.52  --splitting_mode                        input
% 39.63/5.52  --splitting_grd                         true
% 39.63/5.52  --splitting_cvd                         false
% 39.63/5.52  --splitting_cvd_svl                     false
% 39.63/5.52  --splitting_nvd                         32
% 39.63/5.52  --sub_typing                            true
% 39.63/5.52  --prep_gs_sim                           true
% 39.63/5.52  --prep_unflatten                        true
% 39.63/5.52  --prep_res_sim                          true
% 39.63/5.52  --prep_upred                            true
% 39.63/5.52  --prep_sem_filter                       exhaustive
% 39.63/5.52  --prep_sem_filter_out                   false
% 39.63/5.52  --pred_elim                             true
% 39.63/5.52  --res_sim_input                         true
% 39.63/5.52  --eq_ax_congr_red                       true
% 39.63/5.52  --pure_diseq_elim                       true
% 39.63/5.52  --brand_transform                       false
% 39.63/5.52  --non_eq_to_eq                          false
% 39.63/5.52  --prep_def_merge                        true
% 39.63/5.52  --prep_def_merge_prop_impl              false
% 39.63/5.52  --prep_def_merge_mbd                    true
% 39.63/5.52  --prep_def_merge_tr_red                 false
% 39.63/5.52  --prep_def_merge_tr_cl                  false
% 39.63/5.52  --smt_preprocessing                     true
% 39.63/5.52  --smt_ac_axioms                         fast
% 39.63/5.52  --preprocessed_out                      false
% 39.63/5.52  --preprocessed_stats                    false
% 39.63/5.52  
% 39.63/5.52  ------ Abstraction refinement Options
% 39.63/5.52  
% 39.63/5.52  --abstr_ref                             []
% 39.63/5.52  --abstr_ref_prep                        false
% 39.63/5.52  --abstr_ref_until_sat                   false
% 39.63/5.52  --abstr_ref_sig_restrict                funpre
% 39.63/5.52  --abstr_ref_af_restrict_to_split_sk     false
% 39.63/5.52  --abstr_ref_under                       []
% 39.63/5.52  
% 39.63/5.52  ------ SAT Options
% 39.63/5.52  
% 39.63/5.52  --sat_mode                              false
% 39.63/5.52  --sat_fm_restart_options                ""
% 39.63/5.52  --sat_gr_def                            false
% 39.63/5.52  --sat_epr_types                         true
% 39.63/5.52  --sat_non_cyclic_types                  false
% 39.63/5.52  --sat_finite_models                     false
% 39.63/5.52  --sat_fm_lemmas                         false
% 39.63/5.52  --sat_fm_prep                           false
% 39.63/5.52  --sat_fm_uc_incr                        true
% 39.63/5.52  --sat_out_model                         small
% 39.63/5.52  --sat_out_clauses                       false
% 39.63/5.52  
% 39.63/5.52  ------ QBF Options
% 39.63/5.52  
% 39.63/5.52  --qbf_mode                              false
% 39.63/5.52  --qbf_elim_univ                         false
% 39.63/5.52  --qbf_dom_inst                          none
% 39.63/5.52  --qbf_dom_pre_inst                      false
% 39.63/5.52  --qbf_sk_in                             false
% 39.63/5.52  --qbf_pred_elim                         true
% 39.63/5.52  --qbf_split                             512
% 39.63/5.52  
% 39.63/5.52  ------ BMC1 Options
% 39.63/5.52  
% 39.63/5.52  --bmc1_incremental                      false
% 39.63/5.52  --bmc1_axioms                           reachable_all
% 39.63/5.52  --bmc1_min_bound                        0
% 39.63/5.52  --bmc1_max_bound                        -1
% 39.63/5.52  --bmc1_max_bound_default                -1
% 39.63/5.52  --bmc1_symbol_reachability              true
% 39.63/5.52  --bmc1_property_lemmas                  false
% 39.63/5.52  --bmc1_k_induction                      false
% 39.63/5.52  --bmc1_non_equiv_states                 false
% 39.63/5.52  --bmc1_deadlock                         false
% 39.63/5.52  --bmc1_ucm                              false
% 39.63/5.52  --bmc1_add_unsat_core                   none
% 39.63/5.52  --bmc1_unsat_core_children              false
% 39.63/5.52  --bmc1_unsat_core_extrapolate_axioms    false
% 39.63/5.52  --bmc1_out_stat                         full
% 39.63/5.52  --bmc1_ground_init                      false
% 39.63/5.52  --bmc1_pre_inst_next_state              false
% 39.63/5.52  --bmc1_pre_inst_state                   false
% 39.63/5.52  --bmc1_pre_inst_reach_state             false
% 39.63/5.52  --bmc1_out_unsat_core                   false
% 39.63/5.52  --bmc1_aig_witness_out                  false
% 39.63/5.52  --bmc1_verbose                          false
% 39.63/5.52  --bmc1_dump_clauses_tptp                false
% 39.63/5.52  --bmc1_dump_unsat_core_tptp             false
% 39.63/5.52  --bmc1_dump_file                        -
% 39.63/5.52  --bmc1_ucm_expand_uc_limit              128
% 39.63/5.52  --bmc1_ucm_n_expand_iterations          6
% 39.63/5.52  --bmc1_ucm_extend_mode                  1
% 39.63/5.52  --bmc1_ucm_init_mode                    2
% 39.63/5.52  --bmc1_ucm_cone_mode                    none
% 39.63/5.52  --bmc1_ucm_reduced_relation_type        0
% 39.63/5.52  --bmc1_ucm_relax_model                  4
% 39.63/5.52  --bmc1_ucm_full_tr_after_sat            true
% 39.63/5.52  --bmc1_ucm_expand_neg_assumptions       false
% 39.63/5.52  --bmc1_ucm_layered_model                none
% 39.63/5.52  --bmc1_ucm_max_lemma_size               10
% 39.63/5.52  
% 39.63/5.52  ------ AIG Options
% 39.63/5.52  
% 39.63/5.52  --aig_mode                              false
% 39.63/5.52  
% 39.63/5.52  ------ Instantiation Options
% 39.63/5.52  
% 39.63/5.52  --instantiation_flag                    true
% 39.63/5.52  --inst_sos_flag                         true
% 39.63/5.52  --inst_sos_phase                        true
% 39.63/5.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.63/5.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.63/5.52  --inst_lit_sel_side                     none
% 39.63/5.52  --inst_solver_per_active                1400
% 39.63/5.52  --inst_solver_calls_frac                1.
% 39.63/5.52  --inst_passive_queue_type               priority_queues
% 39.63/5.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.63/5.52  --inst_passive_queues_freq              [25;2]
% 39.63/5.52  --inst_dismatching                      true
% 39.63/5.52  --inst_eager_unprocessed_to_passive     true
% 39.63/5.52  --inst_prop_sim_given                   true
% 39.63/5.52  --inst_prop_sim_new                     false
% 39.63/5.52  --inst_subs_new                         false
% 39.63/5.52  --inst_eq_res_simp                      false
% 39.63/5.52  --inst_subs_given                       false
% 39.63/5.52  --inst_orphan_elimination               true
% 39.63/5.52  --inst_learning_loop_flag               true
% 39.63/5.52  --inst_learning_start                   3000
% 39.63/5.52  --inst_learning_factor                  2
% 39.63/5.52  --inst_start_prop_sim_after_learn       3
% 39.63/5.52  --inst_sel_renew                        solver
% 39.63/5.52  --inst_lit_activity_flag                true
% 39.63/5.52  --inst_restr_to_given                   false
% 39.63/5.52  --inst_activity_threshold               500
% 39.63/5.52  --inst_out_proof                        true
% 39.63/5.52  
% 39.63/5.52  ------ Resolution Options
% 39.63/5.52  
% 39.63/5.52  --resolution_flag                       false
% 39.63/5.52  --res_lit_sel                           adaptive
% 39.63/5.52  --res_lit_sel_side                      none
% 39.63/5.52  --res_ordering                          kbo
% 39.63/5.52  --res_to_prop_solver                    active
% 39.63/5.52  --res_prop_simpl_new                    false
% 39.63/5.52  --res_prop_simpl_given                  true
% 39.63/5.52  --res_passive_queue_type                priority_queues
% 39.63/5.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.63/5.52  --res_passive_queues_freq               [15;5]
% 39.63/5.52  --res_forward_subs                      full
% 39.63/5.52  --res_backward_subs                     full
% 39.63/5.52  --res_forward_subs_resolution           true
% 39.63/5.52  --res_backward_subs_resolution          true
% 39.63/5.52  --res_orphan_elimination                true
% 39.63/5.52  --res_time_limit                        2.
% 39.63/5.52  --res_out_proof                         true
% 39.63/5.52  
% 39.63/5.52  ------ Superposition Options
% 39.63/5.52  
% 39.63/5.52  --superposition_flag                    true
% 39.63/5.52  --sup_passive_queue_type                priority_queues
% 39.63/5.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.63/5.52  --sup_passive_queues_freq               [8;1;4]
% 39.63/5.52  --demod_completeness_check              fast
% 39.63/5.52  --demod_use_ground                      true
% 39.63/5.52  --sup_to_prop_solver                    passive
% 39.63/5.52  --sup_prop_simpl_new                    true
% 39.63/5.52  --sup_prop_simpl_given                  true
% 39.63/5.52  --sup_fun_splitting                     true
% 39.63/5.52  --sup_smt_interval                      50000
% 39.63/5.52  
% 39.63/5.52  ------ Superposition Simplification Setup
% 39.63/5.52  
% 39.63/5.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.63/5.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.63/5.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.63/5.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.63/5.52  --sup_full_triv                         [TrivRules;PropSubs]
% 39.63/5.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.63/5.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.63/5.52  --sup_immed_triv                        [TrivRules]
% 39.63/5.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.63/5.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.63/5.52  --sup_immed_bw_main                     []
% 39.63/5.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.63/5.52  --sup_input_triv                        [Unflattening;TrivRules]
% 39.63/5.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.63/5.52  --sup_input_bw                          []
% 39.63/5.52  
% 39.63/5.52  ------ Combination Options
% 39.63/5.52  
% 39.63/5.52  --comb_res_mult                         3
% 39.63/5.52  --comb_sup_mult                         2
% 39.63/5.52  --comb_inst_mult                        10
% 39.63/5.52  
% 39.63/5.52  ------ Debug Options
% 39.63/5.52  
% 39.63/5.52  --dbg_backtrace                         false
% 39.63/5.52  --dbg_dump_prop_clauses                 false
% 39.63/5.52  --dbg_dump_prop_clauses_file            -
% 39.63/5.52  --dbg_out_stat                          false
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  ------ Proving...
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  % SZS status Theorem for theBenchmark.p
% 39.63/5.52  
% 39.63/5.52  % SZS output start CNFRefutation for theBenchmark.p
% 39.63/5.52  
% 39.63/5.52  fof(f10,axiom,(
% 39.63/5.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f56,plain,(
% 39.63/5.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.63/5.52    inference(cnf_transformation,[],[f10])).
% 39.63/5.52  
% 39.63/5.52  fof(f11,axiom,(
% 39.63/5.52    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f57,plain,(
% 39.63/5.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 39.63/5.52    inference(cnf_transformation,[],[f11])).
% 39.63/5.52  
% 39.63/5.52  fof(f2,axiom,(
% 39.63/5.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f44,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.63/5.52    inference(cnf_transformation,[],[f2])).
% 39.63/5.52  
% 39.63/5.52  fof(f12,axiom,(
% 39.63/5.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f58,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.63/5.52    inference(cnf_transformation,[],[f12])).
% 39.63/5.52  
% 39.63/5.52  fof(f77,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 39.63/5.52    inference(definition_unfolding,[],[f44,f58,f58])).
% 39.63/5.52  
% 39.63/5.52  fof(f4,axiom,(
% 39.63/5.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f22,plain,(
% 39.63/5.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 39.63/5.52    inference(rectify,[],[f4])).
% 39.63/5.52  
% 39.63/5.52  fof(f47,plain,(
% 39.63/5.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 39.63/5.52    inference(cnf_transformation,[],[f22])).
% 39.63/5.52  
% 39.63/5.52  fof(f80,plain,(
% 39.63/5.52    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 39.63/5.52    inference(definition_unfolding,[],[f47,f58])).
% 39.63/5.52  
% 39.63/5.52  fof(f15,axiom,(
% 39.63/5.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f61,plain,(
% 39.63/5.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 39.63/5.52    inference(cnf_transformation,[],[f15])).
% 39.63/5.52  
% 39.63/5.52  fof(f3,axiom,(
% 39.63/5.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f30,plain,(
% 39.63/5.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 39.63/5.52    inference(nnf_transformation,[],[f3])).
% 39.63/5.52  
% 39.63/5.52  fof(f45,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 39.63/5.52    inference(cnf_transformation,[],[f30])).
% 39.63/5.52  
% 39.63/5.52  fof(f79,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 39.63/5.52    inference(definition_unfolding,[],[f45,f58])).
% 39.63/5.52  
% 39.63/5.52  fof(f1,axiom,(
% 39.63/5.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f43,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 39.63/5.52    inference(cnf_transformation,[],[f1])).
% 39.63/5.52  
% 39.63/5.52  fof(f6,axiom,(
% 39.63/5.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f51,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.63/5.52    inference(cnf_transformation,[],[f6])).
% 39.63/5.52  
% 39.63/5.52  fof(f76,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 39.63/5.52    inference(definition_unfolding,[],[f51,f58])).
% 39.63/5.52  
% 39.63/5.52  fof(f17,axiom,(
% 39.63/5.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f27,plain,(
% 39.63/5.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 39.63/5.52    inference(ennf_transformation,[],[f17])).
% 39.63/5.52  
% 39.63/5.52  fof(f37,plain,(
% 39.63/5.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 39.63/5.52    inference(nnf_transformation,[],[f27])).
% 39.63/5.52  
% 39.63/5.52  fof(f66,plain,(
% 39.63/5.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 39.63/5.52    inference(cnf_transformation,[],[f37])).
% 39.63/5.52  
% 39.63/5.52  fof(f20,conjecture,(
% 39.63/5.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f21,negated_conjecture,(
% 39.63/5.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 39.63/5.52    inference(negated_conjecture,[],[f20])).
% 39.63/5.52  
% 39.63/5.52  fof(f29,plain,(
% 39.63/5.52    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.63/5.52    inference(ennf_transformation,[],[f21])).
% 39.63/5.52  
% 39.63/5.52  fof(f38,plain,(
% 39.63/5.52    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.63/5.52    inference(nnf_transformation,[],[f29])).
% 39.63/5.52  
% 39.63/5.52  fof(f39,plain,(
% 39.63/5.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.63/5.52    inference(flattening,[],[f38])).
% 39.63/5.52  
% 39.63/5.52  fof(f41,plain,(
% 39.63/5.52    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(X1,sK3) | ~r1_xboole_0(X1,k3_subset_1(X0,sK3))) & (r1_tarski(X1,sK3) | r1_xboole_0(X1,k3_subset_1(X0,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 39.63/5.52    introduced(choice_axiom,[])).
% 39.63/5.52  
% 39.63/5.52  fof(f40,plain,(
% 39.63/5.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK2,X2) | ~r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & (r1_tarski(sK2,X2) | r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 39.63/5.52    introduced(choice_axiom,[])).
% 39.63/5.52  
% 39.63/5.52  fof(f42,plain,(
% 39.63/5.52    ((~r1_tarski(sK2,sK3) | ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & (r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 39.63/5.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f41,f40])).
% 39.63/5.52  
% 39.63/5.52  fof(f73,plain,(
% 39.63/5.52    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 39.63/5.52    inference(cnf_transformation,[],[f42])).
% 39.63/5.52  
% 39.63/5.52  fof(f19,axiom,(
% 39.63/5.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f71,plain,(
% 39.63/5.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 39.63/5.52    inference(cnf_transformation,[],[f19])).
% 39.63/5.52  
% 39.63/5.52  fof(f16,axiom,(
% 39.63/5.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f33,plain,(
% 39.63/5.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 39.63/5.52    inference(nnf_transformation,[],[f16])).
% 39.63/5.52  
% 39.63/5.52  fof(f34,plain,(
% 39.63/5.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 39.63/5.52    inference(rectify,[],[f33])).
% 39.63/5.52  
% 39.63/5.52  fof(f35,plain,(
% 39.63/5.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 39.63/5.52    introduced(choice_axiom,[])).
% 39.63/5.52  
% 39.63/5.52  fof(f36,plain,(
% 39.63/5.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 39.63/5.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 39.63/5.52  
% 39.63/5.52  fof(f62,plain,(
% 39.63/5.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 39.63/5.52    inference(cnf_transformation,[],[f36])).
% 39.63/5.52  
% 39.63/5.52  fof(f86,plain,(
% 39.63/5.52    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 39.63/5.52    inference(equality_resolution,[],[f62])).
% 39.63/5.52  
% 39.63/5.52  fof(f9,axiom,(
% 39.63/5.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f24,plain,(
% 39.63/5.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.63/5.52    inference(ennf_transformation,[],[f9])).
% 39.63/5.52  
% 39.63/5.52  fof(f55,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.63/5.52    inference(cnf_transformation,[],[f24])).
% 39.63/5.52  
% 39.63/5.52  fof(f82,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 39.63/5.52    inference(definition_unfolding,[],[f55,f58])).
% 39.63/5.52  
% 39.63/5.52  fof(f72,plain,(
% 39.63/5.52    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 39.63/5.52    inference(cnf_transformation,[],[f42])).
% 39.63/5.52  
% 39.63/5.52  fof(f74,plain,(
% 39.63/5.52    r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 39.63/5.52    inference(cnf_transformation,[],[f42])).
% 39.63/5.52  
% 39.63/5.52  fof(f18,axiom,(
% 39.63/5.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f28,plain,(
% 39.63/5.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.63/5.52    inference(ennf_transformation,[],[f18])).
% 39.63/5.52  
% 39.63/5.52  fof(f70,plain,(
% 39.63/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.63/5.52    inference(cnf_transformation,[],[f28])).
% 39.63/5.52  
% 39.63/5.52  fof(f14,axiom,(
% 39.63/5.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f25,plain,(
% 39.63/5.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 39.63/5.52    inference(ennf_transformation,[],[f14])).
% 39.63/5.52  
% 39.63/5.52  fof(f26,plain,(
% 39.63/5.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 39.63/5.52    inference(flattening,[],[f25])).
% 39.63/5.52  
% 39.63/5.52  fof(f60,plain,(
% 39.63/5.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 39.63/5.52    inference(cnf_transformation,[],[f26])).
% 39.63/5.52  
% 39.63/5.52  fof(f7,axiom,(
% 39.63/5.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f23,plain,(
% 39.63/5.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 39.63/5.52    inference(ennf_transformation,[],[f7])).
% 39.63/5.52  
% 39.63/5.52  fof(f53,plain,(
% 39.63/5.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 39.63/5.52    inference(cnf_transformation,[],[f23])).
% 39.63/5.52  
% 39.63/5.52  fof(f52,plain,(
% 39.63/5.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 39.63/5.52    inference(cnf_transformation,[],[f23])).
% 39.63/5.52  
% 39.63/5.52  fof(f75,plain,(
% 39.63/5.52    ~r1_tarski(sK2,sK3) | ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 39.63/5.52    inference(cnf_transformation,[],[f42])).
% 39.63/5.52  
% 39.63/5.52  fof(f46,plain,(
% 39.63/5.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 39.63/5.52    inference(cnf_transformation,[],[f30])).
% 39.63/5.52  
% 39.63/5.52  fof(f78,plain,(
% 39.63/5.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.63/5.52    inference(definition_unfolding,[],[f46,f58])).
% 39.63/5.52  
% 39.63/5.52  fof(f5,axiom,(
% 39.63/5.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.63/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.63/5.52  
% 39.63/5.52  fof(f31,plain,(
% 39.63/5.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.63/5.52    inference(nnf_transformation,[],[f5])).
% 39.63/5.52  
% 39.63/5.52  fof(f32,plain,(
% 39.63/5.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.63/5.52    inference(flattening,[],[f31])).
% 39.63/5.52  
% 39.63/5.52  fof(f48,plain,(
% 39.63/5.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.63/5.52    inference(cnf_transformation,[],[f32])).
% 39.63/5.52  
% 39.63/5.52  fof(f84,plain,(
% 39.63/5.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.63/5.52    inference(equality_resolution,[],[f48])).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.63/5.52      inference(cnf_transformation,[],[f56]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_14,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f57]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3477,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_13,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f77]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3285,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_13,c_2]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3748,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3477,c_3285]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3754,plain,
% 39.63/5.52      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_3748,c_3477]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_6132,plain,
% 39.63/5.52      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3754,c_2]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_5,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 39.63/5.52      inference(cnf_transformation,[],[f80]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3751,plain,
% 39.63/5.52      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3477,c_5]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3757,plain,
% 39.63/5.52      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_3754,c_3751]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_6144,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) = k2_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_6132,c_3757]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_6145,plain,
% 39.63/5.52      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_6144,c_5,c_3477]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_17,plain,
% 39.63/5.52      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 39.63/5.52      inference(cnf_transformation,[],[f61]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1775,plain,
% 39.63/5.52      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2909,plain,
% 39.63/5.52      ( r1_xboole_0(X0,k4_xboole_0(X0,X0)) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_5,c_1775]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3624,plain,
% 39.63/5.52      ( r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_2909]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_4,plain,
% 39.63/5.52      ( ~ r1_xboole_0(X0,X1)
% 39.63/5.52      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.63/5.52      inference(cnf_transformation,[],[f79]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1783,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 39.63/5.52      | r1_xboole_0(X0,X1) != iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13624,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k1_xboole_0 ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3624,c_1783]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3614,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3622,plain,
% 39.63/5.52      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_1775]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_4074,plain,
% 39.63/5.52      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_3622]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7301,plain,
% 39.63/5.52      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3614,c_4074]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7312,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) = k4_xboole_0(X0,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3614,c_5]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7334,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(X0,X0) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_7312,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1,plain,
% 39.63/5.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 39.63/5.52      inference(cnf_transformation,[],[f43]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3476,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(X0,X1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_5,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_5092,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_1,c_3476]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7335,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_7334,c_5092]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_0,plain,
% 39.63/5.52      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 39.63/5.52      inference(cnf_transformation,[],[f76]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3618,plain,
% 39.63/5.52      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_0]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7306,plain,
% 39.63/5.52      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3614,c_3618]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7342,plain,
% 39.63/5.52      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_7306,c_7335]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7343,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_7342,c_3618]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7354,plain,
% 39.63/5.52      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_7301,c_7335,c_7343]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13633,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_7354,c_1783]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3621,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8573,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_2,c_3621]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8577,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),X1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_3621]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8726,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_8577,c_7343]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8727,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_8726,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8730,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),X1) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_8573,c_8727]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8731,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_8730,c_13,c_7343]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13687,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))))) = k1_xboole_0 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_13633,c_8731]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3626,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_5]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_12328,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))) = k4_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_8731,c_3626]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7663,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3285,c_7343]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_12336,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_12328,c_7663]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13688,plain,
% 39.63/5.52      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_13687,c_12336]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13714,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_13624,c_13688]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13715,plain,
% 39.63/5.52      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_13714,c_13]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_25,plain,
% 39.63/5.52      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 39.63/5.52      inference(cnf_transformation,[],[f66]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_30,negated_conjecture,
% 39.63/5.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f73]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_669,plain,
% 39.63/5.52      ( r2_hidden(X0,X1)
% 39.63/5.52      | v1_xboole_0(X1)
% 39.63/5.52      | k1_zfmisc_1(sK1) != X1
% 39.63/5.52      | sK3 != X0 ),
% 39.63/5.52      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_670,plain,
% 39.63/5.52      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 39.63/5.52      inference(unflattening,[status(thm)],[c_669]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_27,plain,
% 39.63/5.52      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f71]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_676,plain,
% 39.63/5.52      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 39.63/5.52      inference(forward_subsumption_resolution,
% 39.63/5.52                [status(thm)],
% 39.63/5.52                [c_670,c_27]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1768,plain,
% 39.63/5.52      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_21,plain,
% 39.63/5.52      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.63/5.52      inference(cnf_transformation,[],[f86]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1771,plain,
% 39.63/5.52      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.63/5.52      | r1_tarski(X0,X1) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3281,plain,
% 39.63/5.52      ( r1_tarski(sK3,sK1) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_1768,c_1771]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_12,plain,
% 39.63/5.52      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 39.63/5.52      inference(cnf_transformation,[],[f82]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1778,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 39.63/5.52      | r1_tarski(X0,X1) != iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8060,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3281,c_1778]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8805,plain,
% 39.63/5.52      ( k5_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_8060,c_0]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2798,plain,
% 39.63/5.52      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8812,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK1) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_8805,c_2798]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13782,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,sK1) = k1_xboole_0 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_13715,c_8812]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3474,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_2,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_40285,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_13782,c_3474]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_40496,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK3,X0) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_40285,c_14,c_6145]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_40996,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK3),X0),X1)) = k4_xboole_0(k4_xboole_0(sK3,X0),X1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_40496,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3478,plain,
% 39.63/5.52      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_14,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3495,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_3478,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_41032,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK3),X0),X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_40996,c_14,c_3495]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_31,negated_conjecture,
% 39.63/5.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f72]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_682,plain,
% 39.63/5.52      ( r2_hidden(X0,X1)
% 39.63/5.52      | v1_xboole_0(X1)
% 39.63/5.52      | k1_zfmisc_1(sK1) != X1
% 39.63/5.52      | sK2 != X0 ),
% 39.63/5.52      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_683,plain,
% 39.63/5.52      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 39.63/5.52      inference(unflattening,[status(thm)],[c_682]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_689,plain,
% 39.63/5.52      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 39.63/5.52      inference(forward_subsumption_resolution,
% 39.63/5.52                [status(thm)],
% 39.63/5.52                [c_683,c_27]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1767,plain,
% 39.63/5.52      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3282,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK1) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_1767,c_1771]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8061,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = sK2 ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_3282,c_1778]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8960,plain,
% 39.63/5.52      ( k5_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_8061,c_0]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8967,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_8960,c_2798]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13770,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_13715,c_8967]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_40286,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_13770,c_3474]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_40495,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK2,X0) ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_40286,c_14,c_6145]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_40668,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_1,c_40495]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_117026,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_41032,c_40668]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_29,negated_conjecture,
% 39.63/5.52      ( r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f74]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1769,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK3) = iProver_top
% 39.63/5.52      | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_26,plain,
% 39.63/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.63/5.52      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 39.63/5.52      inference(cnf_transformation,[],[f70]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_695,plain,
% 39.63/5.52      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 39.63/5.52      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 39.63/5.52      | sK3 != X1 ),
% 39.63/5.52      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_696,plain,
% 39.63/5.52      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 39.63/5.52      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 39.63/5.52      inference(unflattening,[status(thm)],[c_695]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1902,plain,
% 39.63/5.52      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 39.63/5.52      inference(equality_resolution,[status(thm)],[c_696]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2057,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK3) = iProver_top
% 39.63/5.52      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_1769,c_1902]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13617,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0
% 39.63/5.52      | r1_tarski(sK2,sK3) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_2057,c_1783]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_16,plain,
% 39.63/5.52      ( r1_tarski(X0,X1)
% 39.63/5.52      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 39.63/5.52      | ~ r1_xboole_0(X0,X2) ),
% 39.63/5.52      inference(cnf_transformation,[],[f60]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1776,plain,
% 39.63/5.52      ( r1_tarski(X0,X1) = iProver_top
% 39.63/5.52      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 39.63/5.52      | r1_xboole_0(X0,X2) != iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_7099,plain,
% 39.63/5.52      ( r1_tarski(X0,X1) != iProver_top
% 39.63/5.52      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 39.63/5.52      | r1_xboole_0(X0,X1) != iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_6145,c_1776]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_100400,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0
% 39.63/5.52      | r1_tarski(sK2,k1_xboole_0) = iProver_top
% 39.63/5.52      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_13617,c_7099]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2445,plain,
% 39.63/5.52      ( ~ r1_xboole_0(X0,k4_xboole_0(sK1,sK3))
% 39.63/5.52      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 39.63/5.52      inference(instantiation,[status(thm)],[c_4]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2447,plain,
% 39.63/5.52      ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
% 39.63/5.52      | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 39.63/5.52      inference(instantiation,[status(thm)],[c_2445]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13736,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK3)
% 39.63/5.52      | k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 39.63/5.52      inference(predicate_to_equality_rev,[status(thm)],[c_13617]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_6168,plain,
% 39.63/5.52      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_1,c_6145]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_40985,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_6168,c_40496]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_41037,plain,
% 39.63/5.52      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_40985,c_13]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_9,plain,
% 39.63/5.52      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 39.63/5.52      inference(cnf_transformation,[],[f53]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1780,plain,
% 39.63/5.52      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 39.63/5.52      | r1_xboole_0(X0,X2) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_42215,plain,
% 39.63/5.52      ( r1_tarski(X0,sK3) != iProver_top
% 39.63/5.52      | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_41037,c_1780]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_42241,plain,
% 39.63/5.52      ( ~ r1_tarski(X0,sK3) | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) ),
% 39.63/5.52      inference(predicate_to_equality_rev,[status(thm)],[c_42215]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_42243,plain,
% 39.63/5.52      ( ~ r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
% 39.63/5.52      inference(instantiation,[status(thm)],[c_42241]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_101292,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 39.63/5.52      inference(global_propositional_subsumption,
% 39.63/5.52                [status(thm)],
% 39.63/5.52                [c_100400,c_2447,c_13736,c_42243]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_101466,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_101292,c_0]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3290,plain,
% 39.63/5.52      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_2,c_1775]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8959,plain,
% 39.63/5.52      ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_8061,c_3290]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13643,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_8959,c_1783]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_17900,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_13643,c_0]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2800,plain,
% 39.63/5.52      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2801,plain,
% 39.63/5.52      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_2800,c_13]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_13761,plain,
% 39.63/5.52      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_13715,c_2801]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_17910,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK2 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_17900,c_13761]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_17922,plain,
% 39.63/5.52      ( k5_xboole_0(sK2,k1_xboole_0) = sK2 ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_17900,c_17910]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_101533,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = sK2 ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_101466,c_17922]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_102382,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK2,X0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_101533,c_14]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_117046,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,X0) ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_117026,c_102382]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_133525,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_6145,c_117046]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_42279,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_40668,c_40496]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_133653,plain,
% 39.63/5.52      ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = sK2 ),
% 39.63/5.52      inference(demodulation,[status(thm)],[c_133525,c_13,c_42279]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_10,plain,
% 39.63/5.52      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f52]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1779,plain,
% 39.63/5.52      ( r1_tarski(X0,X1) = iProver_top
% 39.63/5.52      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_134852,plain,
% 39.63/5.52      ( r1_tarski(X0,sK3) = iProver_top
% 39.63/5.52      | r1_tarski(X0,sK2) != iProver_top ),
% 39.63/5.52      inference(superposition,[status(thm)],[c_133653,c_1779]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_134942,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK3) = iProver_top
% 39.63/5.52      | r1_tarski(sK2,sK2) != iProver_top ),
% 39.63/5.52      inference(instantiation,[status(thm)],[c_134852]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_28,negated_conjecture,
% 39.63/5.52      ( ~ r1_tarski(sK2,sK3) | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
% 39.63/5.52      inference(cnf_transformation,[],[f75]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1770,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK3) != iProver_top
% 39.63/5.52      | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) != iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_2054,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK3) != iProver_top
% 39.63/5.52      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) != iProver_top ),
% 39.63/5.52      inference(light_normalisation,[status(thm)],[c_1770,c_1902]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_3,plain,
% 39.63/5.52      ( r1_xboole_0(X0,X1)
% 39.63/5.52      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 39.63/5.52      inference(cnf_transformation,[],[f78]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1967,plain,
% 39.63/5.52      ( r1_xboole_0(X0,k4_xboole_0(sK1,sK3))
% 39.63/5.52      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) != k1_xboole_0 ),
% 39.63/5.52      inference(instantiation,[status(thm)],[c_3]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1968,plain,
% 39.63/5.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) != k1_xboole_0
% 39.63/5.52      | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_1967]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_1970,plain,
% 39.63/5.52      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK3))) != k1_xboole_0
% 39.63/5.52      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 39.63/5.52      inference(instantiation,[status(thm)],[c_1968]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_8,plain,
% 39.63/5.52      ( r1_tarski(X0,X0) ),
% 39.63/5.52      inference(cnf_transformation,[],[f84]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_85,plain,
% 39.63/5.52      ( r1_tarski(X0,X0) = iProver_top ),
% 39.63/5.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(c_87,plain,
% 39.63/5.52      ( r1_tarski(sK2,sK2) = iProver_top ),
% 39.63/5.52      inference(instantiation,[status(thm)],[c_85]) ).
% 39.63/5.52  
% 39.63/5.52  cnf(contradiction,plain,
% 39.63/5.52      ( $false ),
% 39.63/5.52      inference(minisat,
% 39.63/5.52                [status(thm)],
% 39.63/5.52                [c_134942,c_101292,c_2054,c_1970,c_87]) ).
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  % SZS output end CNFRefutation for theBenchmark.p
% 39.63/5.52  
% 39.63/5.52  ------                               Statistics
% 39.63/5.52  
% 39.63/5.52  ------ General
% 39.63/5.52  
% 39.63/5.52  abstr_ref_over_cycles:                  0
% 39.63/5.52  abstr_ref_under_cycles:                 0
% 39.63/5.52  gc_basic_clause_elim:                   0
% 39.63/5.52  forced_gc_time:                         0
% 39.63/5.52  parsing_time:                           0.007
% 39.63/5.52  unif_index_cands_time:                  0.
% 39.63/5.52  unif_index_add_time:                    0.
% 39.63/5.52  orderings_time:                         0.
% 39.63/5.52  out_proof_time:                         0.021
% 39.63/5.52  total_time:                             4.551
% 39.63/5.52  num_of_symbols:                         46
% 39.63/5.52  num_of_terms:                           180430
% 39.63/5.52  
% 39.63/5.52  ------ Preprocessing
% 39.63/5.52  
% 39.63/5.52  num_of_splits:                          0
% 39.63/5.52  num_of_split_atoms:                     0
% 39.63/5.52  num_of_reused_defs:                     0
% 39.63/5.52  num_eq_ax_congr_red:                    15
% 39.63/5.52  num_of_sem_filtered_clauses:            1
% 39.63/5.52  num_of_subtypes:                        0
% 39.63/5.52  monotx_restored_types:                  0
% 39.63/5.52  sat_num_of_epr_types:                   0
% 39.63/5.52  sat_num_of_non_cyclic_types:            0
% 39.63/5.52  sat_guarded_non_collapsed_types:        0
% 39.63/5.52  num_pure_diseq_elim:                    0
% 39.63/5.52  simp_replaced_by:                       0
% 39.63/5.52  res_preprocessed:                       134
% 39.63/5.52  prep_upred:                             0
% 39.63/5.52  prep_unflattend:                        90
% 39.63/5.52  smt_new_axioms:                         0
% 39.63/5.52  pred_elim_cands:                        3
% 39.63/5.52  pred_elim:                              2
% 39.63/5.52  pred_elim_cl:                           3
% 39.63/5.52  pred_elim_cycles:                       7
% 39.63/5.52  merged_defs:                            24
% 39.63/5.52  merged_defs_ncl:                        0
% 39.63/5.52  bin_hyper_res:                          25
% 39.63/5.52  prep_cycles:                            4
% 39.63/5.52  pred_elim_time:                         0.008
% 39.63/5.52  splitting_time:                         0.
% 39.63/5.52  sem_filter_time:                        0.
% 39.63/5.52  monotx_time:                            0.
% 39.63/5.52  subtype_inf_time:                       0.
% 39.63/5.52  
% 39.63/5.52  ------ Problem properties
% 39.63/5.52  
% 39.63/5.52  clauses:                                28
% 39.63/5.52  conjectures:                            2
% 39.63/5.52  epr:                                    3
% 39.63/5.52  horn:                                   26
% 39.63/5.52  ground:                                 4
% 39.63/5.52  unary:                                  12
% 39.63/5.52  binary:                                 12
% 39.63/5.52  lits:                                   48
% 39.63/5.52  lits_eq:                                18
% 39.63/5.52  fd_pure:                                0
% 39.63/5.52  fd_pseudo:                              0
% 39.63/5.52  fd_cond:                                0
% 39.63/5.52  fd_pseudo_cond:                         3
% 39.63/5.52  ac_symbols:                             0
% 39.63/5.52  
% 39.63/5.52  ------ Propositional Solver
% 39.63/5.52  
% 39.63/5.52  prop_solver_calls:                      54
% 39.63/5.52  prop_fast_solver_calls:                 3066
% 39.63/5.52  smt_solver_calls:                       0
% 39.63/5.52  smt_fast_solver_calls:                  0
% 39.63/5.52  prop_num_of_clauses:                    53385
% 39.63/5.52  prop_preprocess_simplified:             76735
% 39.63/5.52  prop_fo_subsumed:                       23
% 39.63/5.52  prop_solver_time:                       0.
% 39.63/5.52  smt_solver_time:                        0.
% 39.63/5.52  smt_fast_solver_time:                   0.
% 39.63/5.52  prop_fast_solver_time:                  0.
% 39.63/5.52  prop_unsat_core_time:                   0.005
% 39.63/5.52  
% 39.63/5.52  ------ QBF
% 39.63/5.52  
% 39.63/5.52  qbf_q_res:                              0
% 39.63/5.52  qbf_num_tautologies:                    0
% 39.63/5.52  qbf_prep_cycles:                        0
% 39.63/5.52  
% 39.63/5.52  ------ BMC1
% 39.63/5.52  
% 39.63/5.52  bmc1_current_bound:                     -1
% 39.63/5.52  bmc1_last_solved_bound:                 -1
% 39.63/5.52  bmc1_unsat_core_size:                   -1
% 39.63/5.52  bmc1_unsat_core_parents_size:           -1
% 39.63/5.52  bmc1_merge_next_fun:                    0
% 39.63/5.52  bmc1_unsat_core_clauses_time:           0.
% 39.63/5.52  
% 39.63/5.52  ------ Instantiation
% 39.63/5.52  
% 39.63/5.52  inst_num_of_clauses:                    3859
% 39.63/5.52  inst_num_in_passive:                    1610
% 39.63/5.52  inst_num_in_active:                     3352
% 39.63/5.52  inst_num_in_unprocessed:                1283
% 39.63/5.52  inst_num_of_loops:                      4039
% 39.63/5.52  inst_num_of_learning_restarts:          1
% 39.63/5.52  inst_num_moves_active_passive:          687
% 39.63/5.52  inst_lit_activity:                      0
% 39.63/5.52  inst_lit_activity_moves:                0
% 39.63/5.52  inst_num_tautologies:                   0
% 39.63/5.52  inst_num_prop_implied:                  0
% 39.63/5.52  inst_num_existing_simplified:           0
% 39.63/5.52  inst_num_eq_res_simplified:             0
% 39.63/5.52  inst_num_child_elim:                    0
% 39.63/5.52  inst_num_of_dismatching_blockings:      13167
% 39.63/5.52  inst_num_of_non_proper_insts:           13656
% 39.63/5.52  inst_num_of_duplicates:                 0
% 39.63/5.52  inst_inst_num_from_inst_to_res:         0
% 39.63/5.52  inst_dismatching_checking_time:         0.
% 39.63/5.52  
% 39.63/5.52  ------ Resolution
% 39.63/5.52  
% 39.63/5.52  res_num_of_clauses:                     37
% 39.63/5.52  res_num_in_passive:                     37
% 39.63/5.52  res_num_in_active:                      0
% 39.63/5.52  res_num_of_loops:                       138
% 39.63/5.52  res_forward_subset_subsumed:            702
% 39.63/5.52  res_backward_subset_subsumed:           6
% 39.63/5.52  res_forward_subsumed:                   3
% 39.63/5.52  res_backward_subsumed:                  0
% 39.63/5.52  res_forward_subsumption_resolution:     4
% 39.63/5.52  res_backward_subsumption_resolution:    0
% 39.63/5.52  res_clause_to_clause_subsumption:       129527
% 39.63/5.52  res_orphan_elimination:                 0
% 39.63/5.52  res_tautology_del:                      712
% 39.63/5.52  res_num_eq_res_simplified:              0
% 39.63/5.52  res_num_sel_changes:                    0
% 39.63/5.52  res_moves_from_active_to_pass:          0
% 39.63/5.52  
% 39.63/5.52  ------ Superposition
% 39.63/5.52  
% 39.63/5.52  sup_time_total:                         0.
% 39.63/5.52  sup_time_generating:                    0.
% 39.63/5.52  sup_time_sim_full:                      0.
% 39.63/5.52  sup_time_sim_immed:                     0.
% 39.63/5.52  
% 39.63/5.52  sup_num_of_clauses:                     7029
% 39.63/5.52  sup_num_in_active:                      383
% 39.63/5.52  sup_num_in_passive:                     6646
% 39.63/5.52  sup_num_of_loops:                       806
% 39.63/5.52  sup_fw_superposition:                   11308
% 39.63/5.52  sup_bw_superposition:                   15497
% 39.63/5.52  sup_immediate_simplified:               14416
% 39.63/5.52  sup_given_eliminated:                   10
% 39.63/5.52  comparisons_done:                       0
% 39.63/5.52  comparisons_avoided:                    1437
% 39.63/5.52  
% 39.63/5.52  ------ Simplifications
% 39.63/5.52  
% 39.63/5.52  
% 39.63/5.52  sim_fw_subset_subsumed:                 234
% 39.63/5.52  sim_bw_subset_subsumed:                 59
% 39.63/5.52  sim_fw_subsumed:                        3584
% 39.63/5.52  sim_bw_subsumed:                        267
% 39.63/5.52  sim_fw_subsumption_res:                 0
% 39.63/5.52  sim_bw_subsumption_res:                 0
% 39.63/5.52  sim_tautology_del:                      53
% 39.63/5.52  sim_eq_tautology_del:                   3810
% 39.63/5.52  sim_eq_res_simp:                        24
% 39.63/5.52  sim_fw_demodulated:                     10827
% 39.63/5.52  sim_bw_demodulated:                     478
% 39.63/5.52  sim_light_normalised:                   3669
% 39.63/5.52  sim_joinable_taut:                      0
% 39.63/5.52  sim_joinable_simp:                      0
% 39.63/5.52  sim_ac_normalised:                      0
% 39.63/5.52  sim_smt_subsumption:                    0
% 39.63/5.52  
%------------------------------------------------------------------------------
