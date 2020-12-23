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
% DateTime   : Thu Dec  3 11:39:25 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 297 expanded)
%              Number of clauses        :   65 (  90 expanded)
%              Number of leaves         :   20 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  406 (1000 expanded)
%              Number of equality atoms :  164 ( 355 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f34])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f64])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f36,f64,f64])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f62,plain,(
    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1003,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_988,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_991,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_991])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_989,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1252,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_989])).

cnf(c_3342,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK3)) = k4_subset_1(sK3,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_988,c_1252])).

cnf(c_0,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1000,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2106,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1000])).

cnf(c_3619,plain,
    ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3342,c_2106])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1266,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(resolution,[status(thm)],[c_17,c_23])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1082,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
    | r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1269,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_23,c_29,c_1082])).

cnf(c_1456,plain,
    ( r1_tarski(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_13,c_1269])).

cnf(c_2029,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_3,c_1456])).

cnf(c_2030,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

cnf(c_34046,plain,
    ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3619,c_2030])).

cnf(c_34058,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_34046])).

cnf(c_34118,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_34058])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1002,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3618,plain,
    ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3342,c_1002])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1004,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10014,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_1004])).

cnf(c_10027,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
    | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10014])).

cnf(c_461,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_460,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2011,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_461,c_460])).

cnf(c_5391,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | X2 = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[status(thm)],[c_2011,c_6])).

cnf(c_5393,plain,
    ( r2_hidden(sK1(sK3,sK3,sK3),sK3)
    | sK3 = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_5391])).

cnf(c_3330,plain,
    ( k2_subset_1(sK3) != X0
    | k2_subset_1(sK3) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
    | k3_tarski(k2_enumset1(X1,X1,X1,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_3331,plain,
    ( k2_subset_1(sK3) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_subset_1(sK3) != sK3
    | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_3330])).

cnf(c_1180,plain,
    ( X0 != X1
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X1
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2745,plain,
    ( X0 != k3_tarski(k2_enumset1(X1,X1,X1,X2))
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(X1,X1,X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_2746,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = sK3
    | sK3 != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2745])).

cnf(c_1085,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X0
    | k2_subset_1(sK3) != X0
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2742,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(X0,X0,X0,X1))
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    | k2_subset_1(sK3) != k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_2743,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    | k2_subset_1(sK3) != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_1912,plain,
    ( X0 != k4_subset_1(X1,sK4,X2)
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X1,sK4,X2) ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_2207,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X0,sK4,X1)
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
    | k3_tarski(k2_enumset1(X2,X2,X2,X3)) != k4_subset_1(X0,sK4,X1) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_2211,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(sK3,sK4,sK3)
    | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
    | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) != k4_subset_1(sK3,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_469,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_1182,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,X1,X2)
    | k2_subset_1(sK3) != X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_1476,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,sK4,X1)
    | k2_subset_1(sK3) != X1
    | sK4 != sK4
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_1477,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(sK3,sK4,sK3)
    | k2_subset_1(sK3) != sK3
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_1225,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1086,plain,
    ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != sK3
    | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    | k2_subset_1(sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_479,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_68,plain,
    ( ~ r2_hidden(sK1(sK3,sK3,sK3),sK3)
    | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_34,plain,
    ( k2_subset_1(sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_22,negated_conjecture,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34118,c_10027,c_5393,c_3331,c_2746,c_2743,c_2211,c_1477,c_1225,c_1086,c_479,c_68,c_34,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.73/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.73/1.99  
% 11.73/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.73/1.99  
% 11.73/1.99  ------  iProver source info
% 11.73/1.99  
% 11.73/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.73/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.73/1.99  git: non_committed_changes: false
% 11.73/1.99  git: last_make_outside_of_git: false
% 11.73/1.99  
% 11.73/1.99  ------ 
% 11.73/1.99  ------ Parsing...
% 11.73/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.73/1.99  
% 11.73/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.73/1.99  ------ Proving...
% 11.73/1.99  ------ Problem Properties 
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  clauses                                 24
% 11.73/1.99  conjectures                             2
% 11.73/1.99  EPR                                     5
% 11.73/1.99  Horn                                    18
% 11.73/1.99  unary                                   6
% 11.73/1.99  binary                                  6
% 11.73/1.99  lits                                    55
% 11.73/1.99  lits eq                                 9
% 11.73/1.99  fd_pure                                 0
% 11.73/1.99  fd_pseudo                               0
% 11.73/1.99  fd_cond                                 0
% 11.73/1.99  fd_pseudo_cond                          5
% 11.73/1.99  AC symbols                              0
% 11.73/1.99  
% 11.73/1.99  ------ Input Options Time Limit: Unbounded
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  ------ 
% 11.73/1.99  Current options:
% 11.73/1.99  ------ 
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  ------ Proving...
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  % SZS status Theorem for theBenchmark.p
% 11.73/1.99  
% 11.73/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.73/1.99  
% 11.73/1.99  fof(f3,axiom,(
% 11.73/1.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f24,plain,(
% 11.73/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.73/1.99    inference(nnf_transformation,[],[f3])).
% 11.73/1.99  
% 11.73/1.99  fof(f25,plain,(
% 11.73/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.73/1.99    inference(flattening,[],[f24])).
% 11.73/1.99  
% 11.73/1.99  fof(f26,plain,(
% 11.73/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.73/1.99    inference(rectify,[],[f25])).
% 11.73/1.99  
% 11.73/1.99  fof(f27,plain,(
% 11.73/1.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.73/1.99    introduced(choice_axiom,[])).
% 11.73/1.99  
% 11.73/1.99  fof(f28,plain,(
% 11.73/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.73/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 11.73/1.99  
% 11.73/1.99  fof(f43,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f28])).
% 11.73/1.99  
% 11.73/1.99  fof(f7,axiom,(
% 11.73/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f52,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.73/1.99    inference(cnf_transformation,[],[f7])).
% 11.73/1.99  
% 11.73/1.99  fof(f4,axiom,(
% 11.73/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f46,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f4])).
% 11.73/1.99  
% 11.73/1.99  fof(f5,axiom,(
% 11.73/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f47,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f5])).
% 11.73/1.99  
% 11.73/1.99  fof(f63,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f46,f47])).
% 11.73/1.99  
% 11.73/1.99  fof(f64,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 11.73/1.99    inference(definition_unfolding,[],[f52,f63])).
% 11.73/1.99  
% 11.73/1.99  fof(f68,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f43,f64])).
% 11.73/1.99  
% 11.73/1.99  fof(f13,conjecture,(
% 11.73/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f14,negated_conjecture,(
% 11.73/1.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 11.73/1.99    inference(negated_conjecture,[],[f13])).
% 11.73/1.99  
% 11.73/1.99  fof(f19,plain,(
% 11.73/1.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.73/1.99    inference(ennf_transformation,[],[f14])).
% 11.73/1.99  
% 11.73/1.99  fof(f34,plain,(
% 11.73/1.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 11.73/1.99    introduced(choice_axiom,[])).
% 11.73/1.99  
% 11.73/1.99  fof(f35,plain,(
% 11.73/1.99    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 11.73/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f34])).
% 11.73/1.99  
% 11.73/1.99  fof(f61,plain,(
% 11.73/1.99    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 11.73/1.99    inference(cnf_transformation,[],[f35])).
% 11.73/1.99  
% 11.73/1.99  fof(f9,axiom,(
% 11.73/1.99    ! [X0] : k2_subset_1(X0) = X0),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f57,plain,(
% 11.73/1.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.73/1.99    inference(cnf_transformation,[],[f9])).
% 11.73/1.99  
% 11.73/1.99  fof(f10,axiom,(
% 11.73/1.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f58,plain,(
% 11.73/1.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.73/1.99    inference(cnf_transformation,[],[f10])).
% 11.73/1.99  
% 11.73/1.99  fof(f12,axiom,(
% 11.73/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f17,plain,(
% 11.73/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.73/1.99    inference(ennf_transformation,[],[f12])).
% 11.73/1.99  
% 11.73/1.99  fof(f18,plain,(
% 11.73/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.73/1.99    inference(flattening,[],[f17])).
% 11.73/1.99  
% 11.73/1.99  fof(f60,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.73/1.99    inference(cnf_transformation,[],[f18])).
% 11.73/1.99  
% 11.73/1.99  fof(f72,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.73/1.99    inference(definition_unfolding,[],[f60,f64])).
% 11.73/1.99  
% 11.73/1.99  fof(f1,axiom,(
% 11.73/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f36,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f1])).
% 11.73/1.99  
% 11.73/1.99  fof(f65,plain,(
% 11.73/1.99    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 11.73/1.99    inference(definition_unfolding,[],[f36,f64,f64])).
% 11.73/1.99  
% 11.73/1.99  fof(f40,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 11.73/1.99    inference(cnf_transformation,[],[f28])).
% 11.73/1.99  
% 11.73/1.99  fof(f71,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 11.73/1.99    inference(definition_unfolding,[],[f40,f64])).
% 11.73/1.99  
% 11.73/1.99  fof(f75,plain,(
% 11.73/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 11.73/1.99    inference(equality_resolution,[],[f71])).
% 11.73/1.99  
% 11.73/1.99  fof(f2,axiom,(
% 11.73/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f15,plain,(
% 11.73/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.73/1.99    inference(ennf_transformation,[],[f2])).
% 11.73/1.99  
% 11.73/1.99  fof(f20,plain,(
% 11.73/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.73/1.99    inference(nnf_transformation,[],[f15])).
% 11.73/1.99  
% 11.73/1.99  fof(f21,plain,(
% 11.73/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.73/1.99    inference(rectify,[],[f20])).
% 11.73/1.99  
% 11.73/1.99  fof(f22,plain,(
% 11.73/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.73/1.99    introduced(choice_axiom,[])).
% 11.73/1.99  
% 11.73/1.99  fof(f23,plain,(
% 11.73/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.73/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 11.73/1.99  
% 11.73/1.99  fof(f37,plain,(
% 11.73/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f23])).
% 11.73/1.99  
% 11.73/1.99  fof(f6,axiom,(
% 11.73/1.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f29,plain,(
% 11.73/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.73/1.99    inference(nnf_transformation,[],[f6])).
% 11.73/1.99  
% 11.73/1.99  fof(f30,plain,(
% 11.73/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.73/1.99    inference(rectify,[],[f29])).
% 11.73/1.99  
% 11.73/1.99  fof(f31,plain,(
% 11.73/1.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 11.73/1.99    introduced(choice_axiom,[])).
% 11.73/1.99  
% 11.73/1.99  fof(f32,plain,(
% 11.73/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.73/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 11.73/1.99  
% 11.73/1.99  fof(f48,plain,(
% 11.73/1.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.73/1.99    inference(cnf_transformation,[],[f32])).
% 11.73/1.99  
% 11.73/1.99  fof(f77,plain,(
% 11.73/1.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.73/1.99    inference(equality_resolution,[],[f48])).
% 11.73/1.99  
% 11.73/1.99  fof(f8,axiom,(
% 11.73/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f16,plain,(
% 11.73/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.73/1.99    inference(ennf_transformation,[],[f8])).
% 11.73/1.99  
% 11.73/1.99  fof(f33,plain,(
% 11.73/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.73/1.99    inference(nnf_transformation,[],[f16])).
% 11.73/1.99  
% 11.73/1.99  fof(f53,plain,(
% 11.73/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f33])).
% 11.73/1.99  
% 11.73/1.99  fof(f11,axiom,(
% 11.73/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.73/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/1.99  
% 11.73/1.99  fof(f59,plain,(
% 11.73/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.73/1.99    inference(cnf_transformation,[],[f11])).
% 11.73/1.99  
% 11.73/1.99  fof(f42,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 11.73/1.99    inference(cnf_transformation,[],[f28])).
% 11.73/1.99  
% 11.73/1.99  fof(f69,plain,(
% 11.73/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 11.73/1.99    inference(definition_unfolding,[],[f42,f64])).
% 11.73/1.99  
% 11.73/1.99  fof(f73,plain,(
% 11.73/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 11.73/1.99    inference(equality_resolution,[],[f69])).
% 11.73/1.99  
% 11.73/1.99  fof(f44,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.73/1.99    inference(cnf_transformation,[],[f28])).
% 11.73/1.99  
% 11.73/1.99  fof(f67,plain,(
% 11.73/1.99    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.73/1.99    inference(definition_unfolding,[],[f44,f64])).
% 11.73/1.99  
% 11.73/1.99  fof(f62,plain,(
% 11.73/1.99    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))),
% 11.73/1.99    inference(cnf_transformation,[],[f35])).
% 11.73/1.99  
% 11.73/1.99  cnf(c_6,plain,
% 11.73/1.99      ( r2_hidden(sK1(X0,X1,X2),X1)
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X0)
% 11.73/1.99      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 11.73/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1003,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_23,negated_conjecture,
% 11.73/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
% 11.73/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_988,plain,
% 11.73/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK3)) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_18,plain,
% 11.73/1.99      ( k2_subset_1(X0) = X0 ),
% 11.73/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_19,plain,
% 11.73/1.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 11.73/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_991,plain,
% 11.73/1.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1243,plain,
% 11.73/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_18,c_991]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_21,plain,
% 11.73/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.73/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.73/1.99      | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 11.73/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_989,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 11.73/1.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 11.73/1.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1252,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 11.73/1.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1243,c_989]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_3342,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK3)) = k4_subset_1(sK3,sK4,sK3) ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_988,c_1252]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_0,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
% 11.73/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_9,plain,
% 11.73/1.99      ( r2_hidden(X0,X1)
% 11.73/1.99      | r2_hidden(X0,X2)
% 11.73/1.99      | ~ r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 11.73/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1000,plain,
% 11.73/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.73/1.99      | r2_hidden(X0,X2) = iProver_top
% 11.73/1.99      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2106,plain,
% 11.73/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.73/1.99      | r2_hidden(X0,X2) = iProver_top
% 11.73/1.99      | r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_0,c_1000]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_3619,plain,
% 11.73/1.99      ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
% 11.73/1.99      | r2_hidden(X0,sK4) = iProver_top
% 11.73/1.99      | r2_hidden(X0,sK3) = iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_3342,c_2106]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_3,plain,
% 11.73/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.73/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_13,plain,
% 11.73/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.73/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_17,plain,
% 11.73/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.73/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1266,plain,
% 11.73/1.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 11.73/1.99      inference(resolution,[status(thm)],[c_17,c_23]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_20,plain,
% 11.73/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.73/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_29,plain,
% 11.73/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1082,plain,
% 11.73/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK3))
% 11.73/1.99      | r2_hidden(sK4,k1_zfmisc_1(sK3))
% 11.73/1.99      | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1269,plain,
% 11.73/1.99      ( r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
% 11.73/1.99      inference(global_propositional_subsumption,
% 11.73/1.99                [status(thm)],
% 11.73/1.99                [c_1266,c_23,c_29,c_1082]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1456,plain,
% 11.73/1.99      ( r1_tarski(sK4,sK3) ),
% 11.73/1.99      inference(resolution,[status(thm)],[c_13,c_1269]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2029,plain,
% 11.73/1.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK3) ),
% 11.73/1.99      inference(resolution,[status(thm)],[c_3,c_1456]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2030,plain,
% 11.73/1.99      ( r2_hidden(X0,sK4) != iProver_top
% 11.73/1.99      | r2_hidden(X0,sK3) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_2029]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_34046,plain,
% 11.73/1.99      ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) != iProver_top
% 11.73/1.99      | r2_hidden(X0,sK3) = iProver_top ),
% 11.73/1.99      inference(global_propositional_subsumption,
% 11.73/1.99                [status(thm)],
% 11.73/1.99                [c_3619,c_2030]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_34058,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
% 11.73/1.99      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) = iProver_top
% 11.73/1.99      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X1) = iProver_top
% 11.73/1.99      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_1003,c_34046]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_34118,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
% 11.73/1.99      | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) = iProver_top ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_34058]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_7,plain,
% 11.73/1.99      ( ~ r2_hidden(X0,X1)
% 11.73/1.99      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 11.73/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1002,plain,
% 11.73/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.73/1.99      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_3618,plain,
% 11.73/1.99      ( r2_hidden(X0,k4_subset_1(sK3,sK4,sK3)) = iProver_top
% 11.73/1.99      | r2_hidden(X0,sK3) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_3342,c_1002]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_5,plain,
% 11.73/1.99      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
% 11.73/1.99      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 11.73/1.99      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 11.73/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1004,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top ),
% 11.73/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_10014,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(sK3,sK4,sK3)
% 11.73/1.99      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),X0) != iProver_top
% 11.73/1.99      | r2_hidden(sK1(X0,X1,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
% 11.73/1.99      inference(superposition,[status(thm)],[c_3618,c_1004]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_10027,plain,
% 11.73/1.99      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) = k4_subset_1(sK3,sK4,sK3)
% 11.73/1.99      | r2_hidden(sK1(sK3,sK3,k4_subset_1(sK3,sK4,sK3)),sK3) != iProver_top ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_10014]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_461,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_460,plain,( X0 = X0 ),theory(equality) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2011,plain,
% 11.73/1.99      ( X0 != X1 | X1 = X0 ),
% 11.73/1.99      inference(resolution,[status(thm)],[c_461,c_460]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_5391,plain,
% 11.73/1.99      ( r2_hidden(sK1(X0,X1,X2),X1)
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.73/1.99      | r2_hidden(sK1(X0,X1,X2),X0)
% 11.73/1.99      | X2 = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 11.73/1.99      inference(resolution,[status(thm)],[c_2011,c_6]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_5393,plain,
% 11.73/1.99      ( r2_hidden(sK1(sK3,sK3,sK3),sK3)
% 11.73/1.99      | sK3 = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_5391]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_3330,plain,
% 11.73/1.99      ( k2_subset_1(sK3) != X0
% 11.73/1.99      | k2_subset_1(sK3) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
% 11.73/1.99      | k3_tarski(k2_enumset1(X1,X1,X1,X2)) != X0 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_461]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_3331,plain,
% 11.73/1.99      ( k2_subset_1(sK3) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
% 11.73/1.99      | k2_subset_1(sK3) != sK3
% 11.73/1.99      | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_3330]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1180,plain,
% 11.73/1.99      ( X0 != X1
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X1
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_461]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2745,plain,
% 11.73/1.99      ( X0 != k3_tarski(k2_enumset1(X1,X1,X1,X2))
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(X1,X1,X1,X2)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_1180]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2746,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = sK3
% 11.73/1.99      | sK3 != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_2745]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1085,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != X0
% 11.73/1.99      | k2_subset_1(sK3) != X0
% 11.73/1.99      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_461]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2742,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(X0,X0,X0,X1))
% 11.73/1.99      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
% 11.73/1.99      | k2_subset_1(sK3) != k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_1085]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2743,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
% 11.73/1.99      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
% 11.73/1.99      | k2_subset_1(sK3) != k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_2742]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1912,plain,
% 11.73/1.99      ( X0 != k4_subset_1(X1,sK4,X2)
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = X0
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X1,sK4,X2) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_1180]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2207,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(X0,sK4,X1)
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k2_enumset1(X2,X2,X2,X3))
% 11.73/1.99      | k3_tarski(k2_enumset1(X2,X2,X2,X3)) != k4_subset_1(X0,sK4,X1) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_1912]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_2211,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != k4_subset_1(sK3,sK4,sK3)
% 11.73/1.99      | k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3))
% 11.73/1.99      | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) != k4_subset_1(sK3,sK4,sK3) ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_2207]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_469,plain,
% 11.73/1.99      ( X0 != X1
% 11.73/1.99      | X2 != X3
% 11.73/1.99      | X4 != X5
% 11.73/1.99      | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
% 11.73/1.99      theory(equality) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1182,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,X1,X2)
% 11.73/1.99      | k2_subset_1(sK3) != X2
% 11.73/1.99      | sK4 != X1
% 11.73/1.99      | sK3 != X0 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_469]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1476,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(X0,sK4,X1)
% 11.73/1.99      | k2_subset_1(sK3) != X1
% 11.73/1.99      | sK4 != sK4
% 11.73/1.99      | sK3 != X0 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_1182]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1477,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) = k4_subset_1(sK3,sK4,sK3)
% 11.73/1.99      | k2_subset_1(sK3) != sK3
% 11.73/1.99      | sK4 != sK4
% 11.73/1.99      | sK3 != sK3 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_1476]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1225,plain,
% 11.73/1.99      ( sK4 = sK4 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_460]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_1086,plain,
% 11.73/1.99      ( k4_subset_1(sK3,sK4,k2_subset_1(sK3)) != sK3
% 11.73/1.99      | k2_subset_1(sK3) = k4_subset_1(sK3,sK4,k2_subset_1(sK3))
% 11.73/1.99      | k2_subset_1(sK3) != sK3 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_1085]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_479,plain,
% 11.73/1.99      ( sK3 = sK3 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_460]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_68,plain,
% 11.73/1.99      ( ~ r2_hidden(sK1(sK3,sK3,sK3),sK3)
% 11.73/1.99      | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_34,plain,
% 11.73/1.99      ( k2_subset_1(sK3) = sK3 ),
% 11.73/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(c_22,negated_conjecture,
% 11.73/1.99      ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
% 11.73/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.73/1.99  
% 11.73/1.99  cnf(contradiction,plain,
% 11.73/1.99      ( $false ),
% 11.73/1.99      inference(minisat,
% 11.73/1.99                [status(thm)],
% 11.73/1.99                [c_34118,c_10027,c_5393,c_3331,c_2746,c_2743,c_2211,
% 11.73/1.99                 c_1477,c_1225,c_1086,c_479,c_68,c_34,c_22]) ).
% 11.73/1.99  
% 11.73/1.99  
% 11.73/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.73/1.99  
% 11.73/1.99  ------                               Statistics
% 11.73/1.99  
% 11.73/1.99  ------ Selected
% 11.73/1.99  
% 11.73/1.99  total_time:                             1.2
% 11.73/1.99  
%------------------------------------------------------------------------------
