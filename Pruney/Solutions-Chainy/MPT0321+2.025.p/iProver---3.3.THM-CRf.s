%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:42 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  148 (1541 expanded)
%              Number of clauses        :   93 ( 574 expanded)
%              Number of leaves         :   16 ( 289 expanded)
%              Depth                    :   24
%              Number of atoms          :  445 (5726 expanded)
%              Number of equality atoms :  249 (3089 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK4 != sK6
        | sK3 != sK5 )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( sK4 != sK6
      | sK3 != sK5 )
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f42])).

fof(f77,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,
    ( sK4 != sK6
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_955,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_951,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_929,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_6751,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_929])).

cnf(c_6747,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_929])).

cnf(c_12441,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6747,c_929])).

cnf(c_12735,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6751,c_12441])).

cnf(c_36,negated_conjecture,
    ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_936,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6188,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_936])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_935,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7006,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6188,c_935])).

cnf(c_12743,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_12735,c_7006])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_45,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_46,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_14,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_70,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_1001,plain,
    ( k2_zfmisc_1(X0,sK4) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1089,plain,
    ( k2_zfmisc_1(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1226,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4))
    | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1227,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1226])).

cnf(c_518,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2089,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,k1_xboole_0)
    | sK5 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_2090,plain,
    ( sK5 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2089])).

cnf(c_2092,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_2240,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2241,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(c_32,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_930,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2248,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(X0,sK6)) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_930])).

cnf(c_2308,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_2248])).

cnf(c_16399,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12743,c_35,c_34,c_45,c_46,c_72,c_1089,c_1227,c_2092,c_2241,c_2308])).

cnf(c_16405,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | r2_hidden(sK0(sK6,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_16399])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_956,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16829,plain,
    ( r1_tarski(sK6,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_16405,c_956])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_931,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2485,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,X0)) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_931])).

cnf(c_30,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_932,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4137,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK3,sK5) = iProver_top
    | r1_tarski(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_932])).

cnf(c_516,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1008,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1009,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_11646,plain,
    ( r1_tarski(sK3,sK5) = iProver_top
    | r1_tarski(sK6,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4137,c_34,c_45,c_46,c_1009])).

cnf(c_18353,plain,
    ( r1_tarski(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_16829,c_11646])).

cnf(c_2251,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,sK6),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_930])).

cnf(c_947,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3920,plain,
    ( k2_zfmisc_1(X0,sK6) = k2_zfmisc_1(sK3,sK4)
    | r1_tarski(k2_zfmisc_1(X0,sK6),k2_zfmisc_1(sK3,sK4)) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_947])).

cnf(c_3943,plain,
    ( k2_zfmisc_1(X0,sK6) = k2_zfmisc_1(sK3,sK4)
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_3920])).

cnf(c_21098,plain,
    ( k2_zfmisc_1(sK3,sK6) = k2_zfmisc_1(sK3,sK4)
    | r1_tarski(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_18353,c_3943])).

cnf(c_3922,plain,
    ( k2_zfmisc_1(X0,sK6) = k2_zfmisc_1(sK3,sK4)
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(X0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_947])).

cnf(c_8941,plain,
    ( k2_zfmisc_1(sK3,sK6) = k2_zfmisc_1(sK3,sK4)
    | r1_tarski(sK3,sK5) != iProver_top
    | r1_tarski(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_3922])).

cnf(c_3773,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_935])).

cnf(c_6192,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_3773])).

cnf(c_12748,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12735,c_6192])).

cnf(c_1029,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1030,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_16448,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12748,c_35,c_45,c_46,c_1030])).

cnf(c_16454,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r2_hidden(sK0(sK4,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_16448])).

cnf(c_20781,plain,
    ( r1_tarski(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_16454,c_956])).

cnf(c_21418,plain,
    ( k2_zfmisc_1(sK3,sK6) = k2_zfmisc_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21098,c_8941,c_11646,c_16829,c_20781])).

cnf(c_4141,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(X0,sK6)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_932])).

cnf(c_21451,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK4)) != iProver_top
    | r1_tarski(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_21418,c_4141])).

cnf(c_2488,plain,
    ( r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK5,X0),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_931])).

cnf(c_4138,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK5,sK3) = iProver_top
    | r1_tarski(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_932])).

cnf(c_11651,plain,
    ( r1_tarski(sK5,sK3) = iProver_top
    | r1_tarski(sK4,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4138,c_34,c_45,c_46,c_1009])).

cnf(c_21488,plain,
    ( r1_tarski(sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21451,c_11651,c_20781])).

cnf(c_21493,plain,
    ( sK5 = sK3
    | r1_tarski(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_21488,c_947])).

cnf(c_1054,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1355,plain,
    ( ~ r1_tarski(sK5,sK3)
    | ~ r1_tarski(sK3,sK5)
    | sK5 = sK3 ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_1356,plain,
    ( sK5 = sK3
    | r1_tarski(sK5,sK3) != iProver_top
    | r1_tarski(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1355])).

cnf(c_21790,plain,
    ( sK5 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21493,c_1356,c_11646,c_11651,c_16829,c_20781])).

cnf(c_33,negated_conjecture,
    ( sK3 != sK5
    | sK4 != sK6 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_21835,plain,
    ( sK3 != sK3
    | sK6 != sK4 ),
    inference(demodulation,[status(thm)],[c_21790,c_33])).

cnf(c_21837,plain,
    ( sK6 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_21835])).

cnf(c_18352,plain,
    ( sK6 = sK4
    | r1_tarski(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_16829,c_947])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21837,c_20781,c_18352])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:05:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.58/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.58/1.49  
% 7.58/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.49  
% 7.58/1.49  ------  iProver source info
% 7.58/1.49  
% 7.58/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.49  git: non_committed_changes: false
% 7.58/1.49  git: last_make_outside_of_git: false
% 7.58/1.49  
% 7.58/1.49  ------ 
% 7.58/1.49  
% 7.58/1.49  ------ Input Options
% 7.58/1.49  
% 7.58/1.49  --out_options                           all
% 7.58/1.49  --tptp_safe_out                         true
% 7.58/1.49  --problem_path                          ""
% 7.58/1.49  --include_path                          ""
% 7.58/1.49  --clausifier                            res/vclausify_rel
% 7.58/1.49  --clausifier_options                    ""
% 7.58/1.49  --stdin                                 false
% 7.58/1.49  --stats_out                             all
% 7.58/1.49  
% 7.58/1.49  ------ General Options
% 7.58/1.49  
% 7.58/1.49  --fof                                   false
% 7.58/1.49  --time_out_real                         305.
% 7.58/1.49  --time_out_virtual                      -1.
% 7.58/1.49  --symbol_type_check                     false
% 7.58/1.49  --clausify_out                          false
% 7.58/1.49  --sig_cnt_out                           false
% 7.58/1.49  --trig_cnt_out                          false
% 7.58/1.49  --trig_cnt_out_tolerance                1.
% 7.58/1.49  --trig_cnt_out_sk_spl                   false
% 7.58/1.49  --abstr_cl_out                          false
% 7.58/1.49  
% 7.58/1.49  ------ Global Options
% 7.58/1.49  
% 7.58/1.49  --schedule                              default
% 7.58/1.49  --add_important_lit                     false
% 7.58/1.49  --prop_solver_per_cl                    1000
% 7.58/1.49  --min_unsat_core                        false
% 7.58/1.49  --soft_assumptions                      false
% 7.58/1.49  --soft_lemma_size                       3
% 7.58/1.49  --prop_impl_unit_size                   0
% 7.58/1.49  --prop_impl_unit                        []
% 7.58/1.49  --share_sel_clauses                     true
% 7.58/1.49  --reset_solvers                         false
% 7.58/1.49  --bc_imp_inh                            [conj_cone]
% 7.58/1.49  --conj_cone_tolerance                   3.
% 7.58/1.49  --extra_neg_conj                        none
% 7.58/1.49  --large_theory_mode                     true
% 7.58/1.49  --prolific_symb_bound                   200
% 7.58/1.49  --lt_threshold                          2000
% 7.58/1.49  --clause_weak_htbl                      true
% 7.58/1.49  --gc_record_bc_elim                     false
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing Options
% 7.58/1.49  
% 7.58/1.49  --preprocessing_flag                    true
% 7.58/1.49  --time_out_prep_mult                    0.1
% 7.58/1.49  --splitting_mode                        input
% 7.58/1.49  --splitting_grd                         true
% 7.58/1.49  --splitting_cvd                         false
% 7.58/1.49  --splitting_cvd_svl                     false
% 7.58/1.49  --splitting_nvd                         32
% 7.58/1.49  --sub_typing                            true
% 7.58/1.49  --prep_gs_sim                           true
% 7.58/1.49  --prep_unflatten                        true
% 7.58/1.49  --prep_res_sim                          true
% 7.58/1.49  --prep_upred                            true
% 7.58/1.49  --prep_sem_filter                       exhaustive
% 7.58/1.49  --prep_sem_filter_out                   false
% 7.58/1.49  --pred_elim                             true
% 7.58/1.49  --res_sim_input                         true
% 7.58/1.49  --eq_ax_congr_red                       true
% 7.58/1.49  --pure_diseq_elim                       true
% 7.58/1.49  --brand_transform                       false
% 7.58/1.49  --non_eq_to_eq                          false
% 7.58/1.49  --prep_def_merge                        true
% 7.58/1.49  --prep_def_merge_prop_impl              false
% 7.58/1.49  --prep_def_merge_mbd                    true
% 7.58/1.49  --prep_def_merge_tr_red                 false
% 7.58/1.49  --prep_def_merge_tr_cl                  false
% 7.58/1.49  --smt_preprocessing                     true
% 7.58/1.49  --smt_ac_axioms                         fast
% 7.58/1.49  --preprocessed_out                      false
% 7.58/1.49  --preprocessed_stats                    false
% 7.58/1.49  
% 7.58/1.49  ------ Abstraction refinement Options
% 7.58/1.49  
% 7.58/1.49  --abstr_ref                             []
% 7.58/1.49  --abstr_ref_prep                        false
% 7.58/1.49  --abstr_ref_until_sat                   false
% 7.58/1.49  --abstr_ref_sig_restrict                funpre
% 7.58/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.49  --abstr_ref_under                       []
% 7.58/1.49  
% 7.58/1.49  ------ SAT Options
% 7.58/1.49  
% 7.58/1.49  --sat_mode                              false
% 7.58/1.49  --sat_fm_restart_options                ""
% 7.58/1.49  --sat_gr_def                            false
% 7.58/1.49  --sat_epr_types                         true
% 7.58/1.49  --sat_non_cyclic_types                  false
% 7.58/1.49  --sat_finite_models                     false
% 7.58/1.49  --sat_fm_lemmas                         false
% 7.58/1.49  --sat_fm_prep                           false
% 7.58/1.49  --sat_fm_uc_incr                        true
% 7.58/1.49  --sat_out_model                         small
% 7.58/1.49  --sat_out_clauses                       false
% 7.58/1.49  
% 7.58/1.49  ------ QBF Options
% 7.58/1.49  
% 7.58/1.49  --qbf_mode                              false
% 7.58/1.49  --qbf_elim_univ                         false
% 7.58/1.49  --qbf_dom_inst                          none
% 7.58/1.49  --qbf_dom_pre_inst                      false
% 7.58/1.49  --qbf_sk_in                             false
% 7.58/1.49  --qbf_pred_elim                         true
% 7.58/1.49  --qbf_split                             512
% 7.58/1.49  
% 7.58/1.49  ------ BMC1 Options
% 7.58/1.49  
% 7.58/1.49  --bmc1_incremental                      false
% 7.58/1.49  --bmc1_axioms                           reachable_all
% 7.58/1.49  --bmc1_min_bound                        0
% 7.58/1.49  --bmc1_max_bound                        -1
% 7.58/1.49  --bmc1_max_bound_default                -1
% 7.58/1.49  --bmc1_symbol_reachability              true
% 7.58/1.49  --bmc1_property_lemmas                  false
% 7.58/1.49  --bmc1_k_induction                      false
% 7.58/1.49  --bmc1_non_equiv_states                 false
% 7.58/1.49  --bmc1_deadlock                         false
% 7.58/1.49  --bmc1_ucm                              false
% 7.58/1.49  --bmc1_add_unsat_core                   none
% 7.58/1.49  --bmc1_unsat_core_children              false
% 7.58/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.49  --bmc1_out_stat                         full
% 7.58/1.49  --bmc1_ground_init                      false
% 7.58/1.49  --bmc1_pre_inst_next_state              false
% 7.58/1.49  --bmc1_pre_inst_state                   false
% 7.58/1.49  --bmc1_pre_inst_reach_state             false
% 7.58/1.49  --bmc1_out_unsat_core                   false
% 7.58/1.49  --bmc1_aig_witness_out                  false
% 7.58/1.49  --bmc1_verbose                          false
% 7.58/1.49  --bmc1_dump_clauses_tptp                false
% 7.58/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.49  --bmc1_dump_file                        -
% 7.58/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.49  --bmc1_ucm_extend_mode                  1
% 7.58/1.49  --bmc1_ucm_init_mode                    2
% 7.58/1.49  --bmc1_ucm_cone_mode                    none
% 7.58/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.49  --bmc1_ucm_relax_model                  4
% 7.58/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.49  --bmc1_ucm_layered_model                none
% 7.58/1.49  --bmc1_ucm_max_lemma_size               10
% 7.58/1.49  
% 7.58/1.49  ------ AIG Options
% 7.58/1.49  
% 7.58/1.49  --aig_mode                              false
% 7.58/1.49  
% 7.58/1.49  ------ Instantiation Options
% 7.58/1.49  
% 7.58/1.49  --instantiation_flag                    true
% 7.58/1.49  --inst_sos_flag                         true
% 7.58/1.49  --inst_sos_phase                        true
% 7.58/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel_side                     num_symb
% 7.58/1.49  --inst_solver_per_active                1400
% 7.58/1.49  --inst_solver_calls_frac                1.
% 7.58/1.49  --inst_passive_queue_type               priority_queues
% 7.58/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.49  --inst_passive_queues_freq              [25;2]
% 7.58/1.49  --inst_dismatching                      true
% 7.58/1.49  --inst_eager_unprocessed_to_passive     true
% 7.58/1.49  --inst_prop_sim_given                   true
% 7.58/1.49  --inst_prop_sim_new                     false
% 7.58/1.49  --inst_subs_new                         false
% 7.58/1.49  --inst_eq_res_simp                      false
% 7.58/1.49  --inst_subs_given                       false
% 7.58/1.49  --inst_orphan_elimination               true
% 7.58/1.49  --inst_learning_loop_flag               true
% 7.58/1.49  --inst_learning_start                   3000
% 7.58/1.49  --inst_learning_factor                  2
% 7.58/1.49  --inst_start_prop_sim_after_learn       3
% 7.58/1.49  --inst_sel_renew                        solver
% 7.58/1.49  --inst_lit_activity_flag                true
% 7.58/1.49  --inst_restr_to_given                   false
% 7.58/1.49  --inst_activity_threshold               500
% 7.58/1.49  --inst_out_proof                        true
% 7.58/1.49  
% 7.58/1.49  ------ Resolution Options
% 7.58/1.49  
% 7.58/1.49  --resolution_flag                       true
% 7.58/1.49  --res_lit_sel                           adaptive
% 7.58/1.49  --res_lit_sel_side                      none
% 7.58/1.49  --res_ordering                          kbo
% 7.58/1.49  --res_to_prop_solver                    active
% 7.58/1.49  --res_prop_simpl_new                    false
% 7.58/1.49  --res_prop_simpl_given                  true
% 7.58/1.49  --res_passive_queue_type                priority_queues
% 7.58/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.49  --res_passive_queues_freq               [15;5]
% 7.58/1.49  --res_forward_subs                      full
% 7.58/1.49  --res_backward_subs                     full
% 7.58/1.49  --res_forward_subs_resolution           true
% 7.58/1.49  --res_backward_subs_resolution          true
% 7.58/1.49  --res_orphan_elimination                true
% 7.58/1.49  --res_time_limit                        2.
% 7.58/1.49  --res_out_proof                         true
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Options
% 7.58/1.49  
% 7.58/1.49  --superposition_flag                    true
% 7.58/1.49  --sup_passive_queue_type                priority_queues
% 7.58/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.49  --demod_completeness_check              fast
% 7.58/1.49  --demod_use_ground                      true
% 7.58/1.49  --sup_to_prop_solver                    passive
% 7.58/1.49  --sup_prop_simpl_new                    true
% 7.58/1.49  --sup_prop_simpl_given                  true
% 7.58/1.49  --sup_fun_splitting                     true
% 7.58/1.49  --sup_smt_interval                      50000
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Simplification Setup
% 7.58/1.49  
% 7.58/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.49  --sup_immed_triv                        [TrivRules]
% 7.58/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.49  --sup_immed_bw_main                     []
% 7.58/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.49  --sup_input_bw                          []
% 7.58/1.49  
% 7.58/1.49  ------ Combination Options
% 7.58/1.49  
% 7.58/1.49  --comb_res_mult                         3
% 7.58/1.49  --comb_sup_mult                         2
% 7.58/1.49  --comb_inst_mult                        10
% 7.58/1.49  
% 7.58/1.49  ------ Debug Options
% 7.58/1.49  
% 7.58/1.49  --dbg_backtrace                         false
% 7.58/1.49  --dbg_dump_prop_clauses                 false
% 7.58/1.49  --dbg_dump_prop_clauses_file            -
% 7.58/1.49  --dbg_out_stat                          false
% 7.58/1.49  ------ Parsing...
% 7.58/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.49  ------ Proving...
% 7.58/1.49  ------ Problem Properties 
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  clauses                                 35
% 7.58/1.49  conjectures                             4
% 7.58/1.49  EPR                                     8
% 7.58/1.49  Horn                                    27
% 7.58/1.49  unary                                   11
% 7.58/1.49  binary                                  9
% 7.58/1.49  lits                                    78
% 7.58/1.49  lits eq                                 29
% 7.58/1.49  fd_pure                                 0
% 7.58/1.49  fd_pseudo                               0
% 7.58/1.49  fd_cond                                 3
% 7.58/1.49  fd_pseudo_cond                          8
% 7.58/1.49  AC symbols                              0
% 7.58/1.49  
% 7.58/1.49  ------ Schedule dynamic 5 is on 
% 7.58/1.49  
% 7.58/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  ------ 
% 7.58/1.49  Current options:
% 7.58/1.49  ------ 
% 7.58/1.49  
% 7.58/1.49  ------ Input Options
% 7.58/1.49  
% 7.58/1.49  --out_options                           all
% 7.58/1.49  --tptp_safe_out                         true
% 7.58/1.49  --problem_path                          ""
% 7.58/1.49  --include_path                          ""
% 7.58/1.49  --clausifier                            res/vclausify_rel
% 7.58/1.49  --clausifier_options                    ""
% 7.58/1.49  --stdin                                 false
% 7.58/1.49  --stats_out                             all
% 7.58/1.49  
% 7.58/1.49  ------ General Options
% 7.58/1.49  
% 7.58/1.49  --fof                                   false
% 7.58/1.49  --time_out_real                         305.
% 7.58/1.49  --time_out_virtual                      -1.
% 7.58/1.49  --symbol_type_check                     false
% 7.58/1.49  --clausify_out                          false
% 7.58/1.49  --sig_cnt_out                           false
% 7.58/1.49  --trig_cnt_out                          false
% 7.58/1.49  --trig_cnt_out_tolerance                1.
% 7.58/1.49  --trig_cnt_out_sk_spl                   false
% 7.58/1.49  --abstr_cl_out                          false
% 7.58/1.49  
% 7.58/1.49  ------ Global Options
% 7.58/1.49  
% 7.58/1.49  --schedule                              default
% 7.58/1.49  --add_important_lit                     false
% 7.58/1.49  --prop_solver_per_cl                    1000
% 7.58/1.49  --min_unsat_core                        false
% 7.58/1.49  --soft_assumptions                      false
% 7.58/1.49  --soft_lemma_size                       3
% 7.58/1.49  --prop_impl_unit_size                   0
% 7.58/1.49  --prop_impl_unit                        []
% 7.58/1.49  --share_sel_clauses                     true
% 7.58/1.49  --reset_solvers                         false
% 7.58/1.49  --bc_imp_inh                            [conj_cone]
% 7.58/1.49  --conj_cone_tolerance                   3.
% 7.58/1.49  --extra_neg_conj                        none
% 7.58/1.49  --large_theory_mode                     true
% 7.58/1.49  --prolific_symb_bound                   200
% 7.58/1.49  --lt_threshold                          2000
% 7.58/1.49  --clause_weak_htbl                      true
% 7.58/1.49  --gc_record_bc_elim                     false
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing Options
% 7.58/1.49  
% 7.58/1.49  --preprocessing_flag                    true
% 7.58/1.49  --time_out_prep_mult                    0.1
% 7.58/1.49  --splitting_mode                        input
% 7.58/1.49  --splitting_grd                         true
% 7.58/1.49  --splitting_cvd                         false
% 7.58/1.49  --splitting_cvd_svl                     false
% 7.58/1.49  --splitting_nvd                         32
% 7.58/1.49  --sub_typing                            true
% 7.58/1.49  --prep_gs_sim                           true
% 7.58/1.49  --prep_unflatten                        true
% 7.58/1.49  --prep_res_sim                          true
% 7.58/1.49  --prep_upred                            true
% 7.58/1.49  --prep_sem_filter                       exhaustive
% 7.58/1.49  --prep_sem_filter_out                   false
% 7.58/1.49  --pred_elim                             true
% 7.58/1.49  --res_sim_input                         true
% 7.58/1.49  --eq_ax_congr_red                       true
% 7.58/1.49  --pure_diseq_elim                       true
% 7.58/1.49  --brand_transform                       false
% 7.58/1.49  --non_eq_to_eq                          false
% 7.58/1.49  --prep_def_merge                        true
% 7.58/1.49  --prep_def_merge_prop_impl              false
% 7.58/1.49  --prep_def_merge_mbd                    true
% 7.58/1.49  --prep_def_merge_tr_red                 false
% 7.58/1.49  --prep_def_merge_tr_cl                  false
% 7.58/1.49  --smt_preprocessing                     true
% 7.58/1.49  --smt_ac_axioms                         fast
% 7.58/1.49  --preprocessed_out                      false
% 7.58/1.49  --preprocessed_stats                    false
% 7.58/1.49  
% 7.58/1.49  ------ Abstraction refinement Options
% 7.58/1.49  
% 7.58/1.49  --abstr_ref                             []
% 7.58/1.49  --abstr_ref_prep                        false
% 7.58/1.49  --abstr_ref_until_sat                   false
% 7.58/1.49  --abstr_ref_sig_restrict                funpre
% 7.58/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.49  --abstr_ref_under                       []
% 7.58/1.49  
% 7.58/1.49  ------ SAT Options
% 7.58/1.49  
% 7.58/1.49  --sat_mode                              false
% 7.58/1.49  --sat_fm_restart_options                ""
% 7.58/1.49  --sat_gr_def                            false
% 7.58/1.49  --sat_epr_types                         true
% 7.58/1.49  --sat_non_cyclic_types                  false
% 7.58/1.49  --sat_finite_models                     false
% 7.58/1.49  --sat_fm_lemmas                         false
% 7.58/1.49  --sat_fm_prep                           false
% 7.58/1.49  --sat_fm_uc_incr                        true
% 7.58/1.49  --sat_out_model                         small
% 7.58/1.49  --sat_out_clauses                       false
% 7.58/1.49  
% 7.58/1.49  ------ QBF Options
% 7.58/1.49  
% 7.58/1.49  --qbf_mode                              false
% 7.58/1.49  --qbf_elim_univ                         false
% 7.58/1.49  --qbf_dom_inst                          none
% 7.58/1.49  --qbf_dom_pre_inst                      false
% 7.58/1.49  --qbf_sk_in                             false
% 7.58/1.49  --qbf_pred_elim                         true
% 7.58/1.49  --qbf_split                             512
% 7.58/1.49  
% 7.58/1.49  ------ BMC1 Options
% 7.58/1.49  
% 7.58/1.49  --bmc1_incremental                      false
% 7.58/1.49  --bmc1_axioms                           reachable_all
% 7.58/1.49  --bmc1_min_bound                        0
% 7.58/1.49  --bmc1_max_bound                        -1
% 7.58/1.49  --bmc1_max_bound_default                -1
% 7.58/1.49  --bmc1_symbol_reachability              true
% 7.58/1.49  --bmc1_property_lemmas                  false
% 7.58/1.49  --bmc1_k_induction                      false
% 7.58/1.49  --bmc1_non_equiv_states                 false
% 7.58/1.49  --bmc1_deadlock                         false
% 7.58/1.49  --bmc1_ucm                              false
% 7.58/1.49  --bmc1_add_unsat_core                   none
% 7.58/1.49  --bmc1_unsat_core_children              false
% 7.58/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.49  --bmc1_out_stat                         full
% 7.58/1.49  --bmc1_ground_init                      false
% 7.58/1.49  --bmc1_pre_inst_next_state              false
% 7.58/1.49  --bmc1_pre_inst_state                   false
% 7.58/1.49  --bmc1_pre_inst_reach_state             false
% 7.58/1.49  --bmc1_out_unsat_core                   false
% 7.58/1.49  --bmc1_aig_witness_out                  false
% 7.58/1.49  --bmc1_verbose                          false
% 7.58/1.49  --bmc1_dump_clauses_tptp                false
% 7.58/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.49  --bmc1_dump_file                        -
% 7.58/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.49  --bmc1_ucm_extend_mode                  1
% 7.58/1.49  --bmc1_ucm_init_mode                    2
% 7.58/1.49  --bmc1_ucm_cone_mode                    none
% 7.58/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.49  --bmc1_ucm_relax_model                  4
% 7.58/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.49  --bmc1_ucm_layered_model                none
% 7.58/1.49  --bmc1_ucm_max_lemma_size               10
% 7.58/1.49  
% 7.58/1.49  ------ AIG Options
% 7.58/1.49  
% 7.58/1.49  --aig_mode                              false
% 7.58/1.49  
% 7.58/1.49  ------ Instantiation Options
% 7.58/1.49  
% 7.58/1.49  --instantiation_flag                    true
% 7.58/1.49  --inst_sos_flag                         true
% 7.58/1.49  --inst_sos_phase                        true
% 7.58/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.49  --inst_lit_sel_side                     none
% 7.58/1.49  --inst_solver_per_active                1400
% 7.58/1.49  --inst_solver_calls_frac                1.
% 7.58/1.49  --inst_passive_queue_type               priority_queues
% 7.58/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.49  --inst_passive_queues_freq              [25;2]
% 7.58/1.49  --inst_dismatching                      true
% 7.58/1.49  --inst_eager_unprocessed_to_passive     true
% 7.58/1.49  --inst_prop_sim_given                   true
% 7.58/1.49  --inst_prop_sim_new                     false
% 7.58/1.49  --inst_subs_new                         false
% 7.58/1.49  --inst_eq_res_simp                      false
% 7.58/1.49  --inst_subs_given                       false
% 7.58/1.49  --inst_orphan_elimination               true
% 7.58/1.49  --inst_learning_loop_flag               true
% 7.58/1.49  --inst_learning_start                   3000
% 7.58/1.49  --inst_learning_factor                  2
% 7.58/1.49  --inst_start_prop_sim_after_learn       3
% 7.58/1.49  --inst_sel_renew                        solver
% 7.58/1.49  --inst_lit_activity_flag                true
% 7.58/1.49  --inst_restr_to_given                   false
% 7.58/1.49  --inst_activity_threshold               500
% 7.58/1.49  --inst_out_proof                        true
% 7.58/1.49  
% 7.58/1.49  ------ Resolution Options
% 7.58/1.49  
% 7.58/1.49  --resolution_flag                       false
% 7.58/1.49  --res_lit_sel                           adaptive
% 7.58/1.49  --res_lit_sel_side                      none
% 7.58/1.49  --res_ordering                          kbo
% 7.58/1.49  --res_to_prop_solver                    active
% 7.58/1.49  --res_prop_simpl_new                    false
% 7.58/1.49  --res_prop_simpl_given                  true
% 7.58/1.49  --res_passive_queue_type                priority_queues
% 7.58/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.49  --res_passive_queues_freq               [15;5]
% 7.58/1.49  --res_forward_subs                      full
% 7.58/1.49  --res_backward_subs                     full
% 7.58/1.49  --res_forward_subs_resolution           true
% 7.58/1.49  --res_backward_subs_resolution          true
% 7.58/1.49  --res_orphan_elimination                true
% 7.58/1.49  --res_time_limit                        2.
% 7.58/1.49  --res_out_proof                         true
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Options
% 7.58/1.49  
% 7.58/1.49  --superposition_flag                    true
% 7.58/1.49  --sup_passive_queue_type                priority_queues
% 7.58/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.49  --demod_completeness_check              fast
% 7.58/1.49  --demod_use_ground                      true
% 7.58/1.49  --sup_to_prop_solver                    passive
% 7.58/1.49  --sup_prop_simpl_new                    true
% 7.58/1.49  --sup_prop_simpl_given                  true
% 7.58/1.49  --sup_fun_splitting                     true
% 7.58/1.49  --sup_smt_interval                      50000
% 7.58/1.49  
% 7.58/1.49  ------ Superposition Simplification Setup
% 7.58/1.49  
% 7.58/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.49  --sup_immed_triv                        [TrivRules]
% 7.58/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.49  --sup_immed_bw_main                     []
% 7.58/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.49  --sup_input_bw                          []
% 7.58/1.49  
% 7.58/1.49  ------ Combination Options
% 7.58/1.49  
% 7.58/1.49  --comb_res_mult                         3
% 7.58/1.49  --comb_sup_mult                         2
% 7.58/1.49  --comb_inst_mult                        10
% 7.58/1.49  
% 7.58/1.49  ------ Debug Options
% 7.58/1.49  
% 7.58/1.49  --dbg_backtrace                         false
% 7.58/1.49  --dbg_dump_prop_clauses                 false
% 7.58/1.49  --dbg_dump_prop_clauses_file            -
% 7.58/1.49  --dbg_out_stat                          false
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  ------ Proving...
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  % SZS status Theorem for theBenchmark.p
% 7.58/1.49  
% 7.58/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.49  
% 7.58/1.49  fof(f2,axiom,(
% 7.58/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f16,plain,(
% 7.58/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.58/1.49    inference(ennf_transformation,[],[f2])).
% 7.58/1.49  
% 7.58/1.49  fof(f22,plain,(
% 7.58/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.58/1.49    inference(nnf_transformation,[],[f16])).
% 7.58/1.49  
% 7.58/1.49  fof(f23,plain,(
% 7.58/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.58/1.49    inference(rectify,[],[f22])).
% 7.58/1.49  
% 7.58/1.49  fof(f24,plain,(
% 7.58/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f25,plain,(
% 7.58/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.58/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 7.58/1.49  
% 7.58/1.49  fof(f46,plain,(
% 7.58/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f25])).
% 7.58/1.49  
% 7.58/1.49  fof(f3,axiom,(
% 7.58/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f26,plain,(
% 7.58/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.58/1.49    inference(nnf_transformation,[],[f3])).
% 7.58/1.49  
% 7.58/1.49  fof(f27,plain,(
% 7.58/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.58/1.49    inference(flattening,[],[f26])).
% 7.58/1.49  
% 7.58/1.49  fof(f28,plain,(
% 7.58/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.58/1.49    inference(rectify,[],[f27])).
% 7.58/1.49  
% 7.58/1.49  fof(f29,plain,(
% 7.58/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f30,plain,(
% 7.58/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.58/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 7.58/1.49  
% 7.58/1.49  fof(f51,plain,(
% 7.58/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f30])).
% 7.58/1.49  
% 7.58/1.49  fof(f1,axiom,(
% 7.58/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f14,plain,(
% 7.58/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 7.58/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.58/1.49  
% 7.58/1.49  fof(f15,plain,(
% 7.58/1.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 7.58/1.49    inference(ennf_transformation,[],[f14])).
% 7.58/1.49  
% 7.58/1.49  fof(f44,plain,(
% 7.58/1.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f15])).
% 7.58/1.49  
% 7.58/1.49  fof(f4,axiom,(
% 7.58/1.49    v1_xboole_0(k1_xboole_0)),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f54,plain,(
% 7.58/1.49    v1_xboole_0(k1_xboole_0)),
% 7.58/1.49    inference(cnf_transformation,[],[f4])).
% 7.58/1.49  
% 7.58/1.49  fof(f12,conjecture,(
% 7.58/1.49    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f13,negated_conjecture,(
% 7.58/1.49    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.58/1.49    inference(negated_conjecture,[],[f12])).
% 7.58/1.49  
% 7.58/1.49  fof(f20,plain,(
% 7.58/1.49    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.58/1.49    inference(ennf_transformation,[],[f13])).
% 7.58/1.49  
% 7.58/1.49  fof(f21,plain,(
% 7.58/1.49    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.58/1.49    inference(flattening,[],[f20])).
% 7.58/1.49  
% 7.58/1.49  fof(f42,plain,(
% 7.58/1.49    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK4 != sK6 | sK3 != sK5) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6))),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f43,plain,(
% 7.58/1.49    (sK4 != sK6 | sK3 != sK5) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6)),
% 7.58/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f42])).
% 7.58/1.49  
% 7.58/1.49  fof(f77,plain,(
% 7.58/1.49    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6)),
% 7.58/1.49    inference(cnf_transformation,[],[f43])).
% 7.58/1.49  
% 7.58/1.49  fof(f8,axiom,(
% 7.58/1.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f38,plain,(
% 7.58/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.58/1.49    inference(nnf_transformation,[],[f8])).
% 7.58/1.49  
% 7.58/1.49  fof(f39,plain,(
% 7.58/1.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.58/1.49    inference(flattening,[],[f38])).
% 7.58/1.49  
% 7.58/1.49  fof(f69,plain,(
% 7.58/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f39])).
% 7.58/1.49  
% 7.58/1.49  fof(f68,plain,(
% 7.58/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.58/1.49    inference(cnf_transformation,[],[f39])).
% 7.58/1.49  
% 7.58/1.49  fof(f78,plain,(
% 7.58/1.49    k1_xboole_0 != sK3),
% 7.58/1.49    inference(cnf_transformation,[],[f43])).
% 7.58/1.49  
% 7.58/1.49  fof(f79,plain,(
% 7.58/1.49    k1_xboole_0 != sK4),
% 7.58/1.49    inference(cnf_transformation,[],[f43])).
% 7.58/1.49  
% 7.58/1.49  fof(f9,axiom,(
% 7.58/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f40,plain,(
% 7.58/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.58/1.49    inference(nnf_transformation,[],[f9])).
% 7.58/1.49  
% 7.58/1.49  fof(f41,plain,(
% 7.58/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.58/1.49    inference(flattening,[],[f40])).
% 7.58/1.49  
% 7.58/1.49  fof(f70,plain,(
% 7.58/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f41])).
% 7.58/1.49  
% 7.58/1.49  fof(f71,plain,(
% 7.58/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.58/1.49    inference(cnf_transformation,[],[f41])).
% 7.58/1.49  
% 7.58/1.49  fof(f94,plain,(
% 7.58/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.58/1.49    inference(equality_resolution,[],[f71])).
% 7.58/1.49  
% 7.58/1.49  fof(f6,axiom,(
% 7.58/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f58,plain,(
% 7.58/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f6])).
% 7.58/1.49  
% 7.58/1.49  fof(f5,axiom,(
% 7.58/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f31,plain,(
% 7.58/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.49    inference(nnf_transformation,[],[f5])).
% 7.58/1.49  
% 7.58/1.49  fof(f32,plain,(
% 7.58/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.49    inference(flattening,[],[f31])).
% 7.58/1.49  
% 7.58/1.49  fof(f57,plain,(
% 7.58/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f32])).
% 7.58/1.49  
% 7.58/1.49  fof(f11,axiom,(
% 7.58/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f19,plain,(
% 7.58/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 7.58/1.49    inference(ennf_transformation,[],[f11])).
% 7.58/1.49  
% 7.58/1.49  fof(f75,plain,(
% 7.58/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f19])).
% 7.58/1.49  
% 7.58/1.49  fof(f47,plain,(
% 7.58/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f25])).
% 7.58/1.49  
% 7.58/1.49  fof(f76,plain,(
% 7.58/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f19])).
% 7.58/1.49  
% 7.58/1.49  fof(f10,axiom,(
% 7.58/1.49    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 7.58/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f18,plain,(
% 7.58/1.49    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 7.58/1.49    inference(ennf_transformation,[],[f10])).
% 7.58/1.49  
% 7.58/1.49  fof(f73,plain,(
% 7.58/1.49    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 7.58/1.49    inference(cnf_transformation,[],[f18])).
% 7.58/1.49  
% 7.58/1.49  fof(f80,plain,(
% 7.58/1.49    sK4 != sK6 | sK3 != sK5),
% 7.58/1.49    inference(cnf_transformation,[],[f43])).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_955,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.58/1.49      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_6,plain,
% 7.58/1.49      ( r2_hidden(sK1(X0,X1,X2),X0)
% 7.58/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.58/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.58/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_951,plain,
% 7.58/1.49      ( k3_xboole_0(X0,X1) = X2
% 7.58/1.49      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 7.58/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_0,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_10,plain,
% 7.58/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_321,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 7.58/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_322,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.58/1.49      inference(unflattening,[status(thm)],[c_321]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_929,plain,
% 7.58/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_6751,plain,
% 7.58/1.49      ( k3_xboole_0(k1_xboole_0,X0) = X1
% 7.58/1.49      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_951,c_929]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_6747,plain,
% 7.58/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 7.58/1.49      | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_951,c_929]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12441,plain,
% 7.58/1.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_6747,c_929]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12735,plain,
% 7.58/1.49      ( k1_xboole_0 = X0
% 7.58/1.49      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 7.58/1.49      inference(demodulation,[status(thm)],[c_6751,c_12441]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_36,negated_conjecture,
% 7.58/1.49      ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
% 7.58/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_23,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,X1)
% 7.58/1.49      | ~ r2_hidden(X2,X3)
% 7.58/1.49      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.58/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_936,plain,
% 7.58/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.58/1.49      | r2_hidden(X2,X3) != iProver_top
% 7.58/1.49      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_6188,plain,
% 7.58/1.49      ( r2_hidden(X0,sK5) != iProver_top
% 7.58/1.49      | r2_hidden(X1,sK6) != iProver_top
% 7.58/1.49      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_36,c_936]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_24,plain,
% 7.58/1.49      ( r2_hidden(X0,X1)
% 7.58/1.49      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.58/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_935,plain,
% 7.58/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.58/1.49      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_7006,plain,
% 7.58/1.49      ( r2_hidden(X0,sK5) != iProver_top
% 7.58/1.49      | r2_hidden(X1,sK6) != iProver_top
% 7.58/1.49      | r2_hidden(X1,sK4) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_6188,c_935]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12743,plain,
% 7.58/1.49      ( sK5 = k1_xboole_0
% 7.58/1.49      | r2_hidden(X0,sK6) != iProver_top
% 7.58/1.49      | r2_hidden(X0,sK4) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_12735,c_7006]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_35,negated_conjecture,
% 7.58/1.49      ( k1_xboole_0 != sK3 ),
% 7.58/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_34,negated_conjecture,
% 7.58/1.49      ( k1_xboole_0 != sK4 ),
% 7.58/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_28,plain,
% 7.58/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.58/1.49      | k1_xboole_0 = X1
% 7.58/1.49      | k1_xboole_0 = X0 ),
% 7.58/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_45,plain,
% 7.58/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.58/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_27,plain,
% 7.58/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.58/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_46,plain,
% 7.58/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_27]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_14,plain,
% 7.58/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_70,plain,
% 7.58/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_72,plain,
% 7.58/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_70]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1001,plain,
% 7.58/1.49      ( k2_zfmisc_1(X0,sK4) != k1_xboole_0
% 7.58/1.49      | k1_xboole_0 = X0
% 7.58/1.49      | k1_xboole_0 = sK4 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1089,plain,
% 7.58/1.49      ( k2_zfmisc_1(sK3,sK4) != k1_xboole_0
% 7.58/1.49      | k1_xboole_0 = sK3
% 7.58/1.49      | k1_xboole_0 = sK4 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_1001]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_11,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.58/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1226,plain,
% 7.58/1.49      ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
% 7.58/1.49      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4))
% 7.58/1.49      | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1227,plain,
% 7.58/1.49      ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0) != iProver_top
% 7.58/1.49      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_1226]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_518,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.58/1.49      theory(equality) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2089,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,X1)
% 7.58/1.49      | r1_tarski(sK5,k1_xboole_0)
% 7.58/1.49      | sK5 != X0
% 7.58/1.49      | k1_xboole_0 != X1 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_518]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2090,plain,
% 7.58/1.49      ( sK5 != X0
% 7.58/1.49      | k1_xboole_0 != X1
% 7.58/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.58/1.49      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_2089]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2092,plain,
% 7.58/1.49      ( sK5 != k1_xboole_0
% 7.58/1.49      | k1_xboole_0 != k1_xboole_0
% 7.58/1.49      | r1_tarski(sK5,k1_xboole_0) = iProver_top
% 7.58/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_2090]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2240,plain,
% 7.58/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2241,plain,
% 7.58/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_2240]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_32,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,X1)
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 7.58/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_930,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2248,plain,
% 7.58/1.49      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(X0,sK6)) = iProver_top
% 7.58/1.49      | r1_tarski(sK5,X0) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_36,c_930]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2308,plain,
% 7.58/1.49      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k1_xboole_0) = iProver_top
% 7.58/1.49      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_27,c_2248]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16399,plain,
% 7.58/1.49      ( r2_hidden(X0,sK6) != iProver_top
% 7.58/1.49      | r2_hidden(X0,sK4) = iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_12743,c_35,c_34,c_45,c_46,c_72,c_1089,c_1227,c_2092,
% 7.58/1.49                 c_2241,c_2308]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16405,plain,
% 7.58/1.49      ( r1_tarski(sK6,X0) = iProver_top
% 7.58/1.49      | r2_hidden(sK0(sK6,X0),sK4) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_955,c_16399]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_956,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.58/1.49      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16829,plain,
% 7.58/1.49      ( r1_tarski(sK6,sK4) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_16405,c_956]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_31,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,X1)
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 7.58/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_931,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2485,plain,
% 7.58/1.49      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,X0)) = iProver_top
% 7.58/1.49      | r1_tarski(sK6,X0) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_36,c_931]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_30,plain,
% 7.58/1.49      ( r1_tarski(X0,X1)
% 7.58/1.49      | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
% 7.58/1.49      | k1_xboole_0 = X2 ),
% 7.58/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_932,plain,
% 7.58/1.49      ( k1_xboole_0 = X0
% 7.58/1.49      | r1_tarski(X1,X2) = iProver_top
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_4137,plain,
% 7.58/1.49      ( sK4 = k1_xboole_0
% 7.58/1.49      | r1_tarski(sK3,sK5) = iProver_top
% 7.58/1.49      | r1_tarski(sK6,sK4) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_2485,c_932]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_516,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1008,plain,
% 7.58/1.49      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_516]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1009,plain,
% 7.58/1.49      ( sK4 != k1_xboole_0
% 7.58/1.49      | k1_xboole_0 = sK4
% 7.58/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_1008]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_11646,plain,
% 7.58/1.49      ( r1_tarski(sK3,sK5) = iProver_top
% 7.58/1.49      | r1_tarski(sK6,sK4) != iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_4137,c_34,c_45,c_46,c_1009]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_18353,plain,
% 7.58/1.49      ( r1_tarski(sK3,sK5) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_16829,c_11646]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2251,plain,
% 7.58/1.49      ( r1_tarski(X0,sK5) != iProver_top
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(X0,sK6),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_36,c_930]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_947,plain,
% 7.58/1.49      ( X0 = X1
% 7.58/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.58/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_3920,plain,
% 7.58/1.49      ( k2_zfmisc_1(X0,sK6) = k2_zfmisc_1(sK3,sK4)
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(X0,sK6),k2_zfmisc_1(sK3,sK4)) != iProver_top
% 7.58/1.49      | r1_tarski(sK5,X0) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_2248,c_947]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_3943,plain,
% 7.58/1.49      ( k2_zfmisc_1(X0,sK6) = k2_zfmisc_1(sK3,sK4)
% 7.58/1.49      | r1_tarski(X0,sK5) != iProver_top
% 7.58/1.49      | r1_tarski(sK5,X0) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_2251,c_3920]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21098,plain,
% 7.58/1.49      ( k2_zfmisc_1(sK3,sK6) = k2_zfmisc_1(sK3,sK4)
% 7.58/1.49      | r1_tarski(sK5,sK3) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_18353,c_3943]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_3922,plain,
% 7.58/1.49      ( k2_zfmisc_1(X0,sK6) = k2_zfmisc_1(sK3,sK4)
% 7.58/1.49      | r1_tarski(X0,sK5) != iProver_top
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(X0,sK6)) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_2251,c_947]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_8941,plain,
% 7.58/1.49      ( k2_zfmisc_1(sK3,sK6) = k2_zfmisc_1(sK3,sK4)
% 7.58/1.49      | r1_tarski(sK3,sK5) != iProver_top
% 7.58/1.49      | r1_tarski(sK4,sK6) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_931,c_3922]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_3773,plain,
% 7.58/1.49      ( r2_hidden(X0,sK6) = iProver_top
% 7.58/1.49      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_36,c_935]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_6192,plain,
% 7.58/1.49      ( r2_hidden(X0,sK3) != iProver_top
% 7.58/1.49      | r2_hidden(X1,sK6) = iProver_top
% 7.58/1.49      | r2_hidden(X1,sK4) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_936,c_3773]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12748,plain,
% 7.58/1.49      ( sK3 = k1_xboole_0
% 7.58/1.49      | r2_hidden(X0,sK6) = iProver_top
% 7.58/1.49      | r2_hidden(X0,sK4) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_12735,c_6192]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1029,plain,
% 7.58/1.49      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_516]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1030,plain,
% 7.58/1.49      ( sK3 != k1_xboole_0
% 7.58/1.49      | k1_xboole_0 = sK3
% 7.58/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_1029]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16448,plain,
% 7.58/1.49      ( r2_hidden(X0,sK6) = iProver_top
% 7.58/1.49      | r2_hidden(X0,sK4) != iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_12748,c_35,c_45,c_46,c_1030]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16454,plain,
% 7.58/1.49      ( r1_tarski(sK4,X0) = iProver_top
% 7.58/1.49      | r2_hidden(sK0(sK4,X0),sK6) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_955,c_16448]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_20781,plain,
% 7.58/1.49      ( r1_tarski(sK4,sK6) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_16454,c_956]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21418,plain,
% 7.58/1.49      ( k2_zfmisc_1(sK3,sK6) = k2_zfmisc_1(sK3,sK4) ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_21098,c_8941,c_11646,c_16829,c_20781]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_4141,plain,
% 7.58/1.49      ( sK6 = k1_xboole_0
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(X0,sK6)) != iProver_top
% 7.58/1.49      | r1_tarski(sK5,X0) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_36,c_932]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21451,plain,
% 7.58/1.49      ( sK6 = k1_xboole_0
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK4)) != iProver_top
% 7.58/1.49      | r1_tarski(sK5,sK3) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_21418,c_4141]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_2488,plain,
% 7.58/1.49      ( r1_tarski(X0,sK6) != iProver_top
% 7.58/1.49      | r1_tarski(k2_zfmisc_1(sK5,X0),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_36,c_931]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_4138,plain,
% 7.58/1.49      ( sK4 = k1_xboole_0
% 7.58/1.49      | r1_tarski(sK5,sK3) = iProver_top
% 7.58/1.49      | r1_tarski(sK4,sK6) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_2488,c_932]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_11651,plain,
% 7.58/1.49      ( r1_tarski(sK5,sK3) = iProver_top
% 7.58/1.49      | r1_tarski(sK4,sK6) != iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_4138,c_34,c_45,c_46,c_1009]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21488,plain,
% 7.58/1.49      ( r1_tarski(sK5,sK3) = iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_21451,c_11651,c_20781]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21493,plain,
% 7.58/1.49      ( sK5 = sK3 | r1_tarski(sK3,sK5) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_21488,c_947]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1054,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1355,plain,
% 7.58/1.49      ( ~ r1_tarski(sK5,sK3) | ~ r1_tarski(sK3,sK5) | sK5 = sK3 ),
% 7.58/1.49      inference(instantiation,[status(thm)],[c_1054]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1356,plain,
% 7.58/1.49      ( sK5 = sK3
% 7.58/1.49      | r1_tarski(sK5,sK3) != iProver_top
% 7.58/1.49      | r1_tarski(sK3,sK5) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_1355]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21790,plain,
% 7.58/1.49      ( sK5 = sK3 ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_21493,c_1356,c_11646,c_11651,c_16829,c_20781]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_33,negated_conjecture,
% 7.58/1.49      ( sK3 != sK5 | sK4 != sK6 ),
% 7.58/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21835,plain,
% 7.58/1.49      ( sK3 != sK3 | sK6 != sK4 ),
% 7.58/1.49      inference(demodulation,[status(thm)],[c_21790,c_33]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_21837,plain,
% 7.58/1.49      ( sK6 != sK4 ),
% 7.58/1.49      inference(equality_resolution_simp,[status(thm)],[c_21835]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_18352,plain,
% 7.58/1.49      ( sK6 = sK4 | r1_tarski(sK4,sK6) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_16829,c_947]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(contradiction,plain,
% 7.58/1.49      ( $false ),
% 7.58/1.49      inference(minisat,[status(thm)],[c_21837,c_20781,c_18352]) ).
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.49  
% 7.58/1.49  ------                               Statistics
% 7.58/1.49  
% 7.58/1.49  ------ General
% 7.58/1.49  
% 7.58/1.49  abstr_ref_over_cycles:                  0
% 7.58/1.49  abstr_ref_under_cycles:                 0
% 7.58/1.49  gc_basic_clause_elim:                   0
% 7.58/1.49  forced_gc_time:                         0
% 7.58/1.49  parsing_time:                           0.007
% 7.58/1.49  unif_index_cands_time:                  0.
% 7.58/1.49  unif_index_add_time:                    0.
% 7.58/1.49  orderings_time:                         0.
% 7.58/1.49  out_proof_time:                         0.017
% 7.58/1.49  total_time:                             0.691
% 7.58/1.49  num_of_symbols:                         46
% 7.58/1.49  num_of_terms:                           24235
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing
% 7.58/1.49  
% 7.58/1.49  num_of_splits:                          0
% 7.58/1.49  num_of_split_atoms:                     0
% 7.58/1.49  num_of_reused_defs:                     0
% 7.58/1.49  num_eq_ax_congr_red:                    48
% 7.58/1.49  num_of_sem_filtered_clauses:            1
% 7.58/1.49  num_of_subtypes:                        0
% 7.58/1.49  monotx_restored_types:                  0
% 7.58/1.49  sat_num_of_epr_types:                   0
% 7.58/1.49  sat_num_of_non_cyclic_types:            0
% 7.58/1.49  sat_guarded_non_collapsed_types:        0
% 7.58/1.49  num_pure_diseq_elim:                    0
% 7.58/1.49  simp_replaced_by:                       0
% 7.58/1.49  res_preprocessed:                       152
% 7.58/1.49  prep_upred:                             0
% 7.58/1.49  prep_unflattend:                        1
% 7.58/1.49  smt_new_axioms:                         0
% 7.58/1.49  pred_elim_cands:                        2
% 7.58/1.49  pred_elim:                              1
% 7.58/1.49  pred_elim_cl:                           1
% 7.58/1.49  pred_elim_cycles:                       3
% 7.58/1.49  merged_defs:                            0
% 7.58/1.49  merged_defs_ncl:                        0
% 7.58/1.49  bin_hyper_res:                          0
% 7.58/1.49  prep_cycles:                            4
% 7.58/1.49  pred_elim_time:                         0.001
% 7.58/1.49  splitting_time:                         0.
% 7.58/1.49  sem_filter_time:                        0.
% 7.58/1.49  monotx_time:                            0.
% 7.58/1.49  subtype_inf_time:                       0.
% 7.58/1.49  
% 7.58/1.49  ------ Problem properties
% 7.58/1.49  
% 7.58/1.49  clauses:                                35
% 7.58/1.49  conjectures:                            4
% 7.58/1.49  epr:                                    8
% 7.58/1.49  horn:                                   27
% 7.58/1.49  ground:                                 4
% 7.58/1.49  unary:                                  11
% 7.58/1.49  binary:                                 9
% 7.58/1.49  lits:                                   78
% 7.58/1.49  lits_eq:                                29
% 7.58/1.49  fd_pure:                                0
% 7.58/1.49  fd_pseudo:                              0
% 7.58/1.49  fd_cond:                                3
% 7.58/1.49  fd_pseudo_cond:                         8
% 7.58/1.49  ac_symbols:                             0
% 7.58/1.49  
% 7.58/1.49  ------ Propositional Solver
% 7.58/1.49  
% 7.58/1.49  prop_solver_calls:                      32
% 7.58/1.49  prop_fast_solver_calls:                 1099
% 7.58/1.49  smt_solver_calls:                       0
% 7.58/1.49  smt_fast_solver_calls:                  0
% 7.58/1.49  prop_num_of_clauses:                    11585
% 7.58/1.49  prop_preprocess_simplified:             25317
% 7.58/1.49  prop_fo_subsumed:                       22
% 7.58/1.49  prop_solver_time:                       0.
% 7.58/1.49  smt_solver_time:                        0.
% 7.58/1.49  smt_fast_solver_time:                   0.
% 7.58/1.49  prop_fast_solver_time:                  0.
% 7.58/1.49  prop_unsat_core_time:                   0.001
% 7.58/1.49  
% 7.58/1.49  ------ QBF
% 7.58/1.49  
% 7.58/1.49  qbf_q_res:                              0
% 7.58/1.49  qbf_num_tautologies:                    0
% 7.58/1.49  qbf_prep_cycles:                        0
% 7.58/1.49  
% 7.58/1.49  ------ BMC1
% 7.58/1.49  
% 7.58/1.49  bmc1_current_bound:                     -1
% 7.58/1.49  bmc1_last_solved_bound:                 -1
% 7.58/1.49  bmc1_unsat_core_size:                   -1
% 7.58/1.49  bmc1_unsat_core_parents_size:           -1
% 7.58/1.49  bmc1_merge_next_fun:                    0
% 7.58/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.58/1.49  
% 7.58/1.49  ------ Instantiation
% 7.58/1.49  
% 7.58/1.49  inst_num_of_clauses:                    4558
% 7.58/1.49  inst_num_in_passive:                    3676
% 7.58/1.49  inst_num_in_active:                     587
% 7.58/1.49  inst_num_in_unprocessed:                303
% 7.58/1.49  inst_num_of_loops:                      630
% 7.58/1.49  inst_num_of_learning_restarts:          0
% 7.58/1.49  inst_num_moves_active_passive:          43
% 7.58/1.49  inst_lit_activity:                      0
% 7.58/1.49  inst_lit_activity_moves:                0
% 7.58/1.49  inst_num_tautologies:                   0
% 7.58/1.49  inst_num_prop_implied:                  0
% 7.58/1.49  inst_num_existing_simplified:           0
% 7.58/1.49  inst_num_eq_res_simplified:             0
% 7.58/1.49  inst_num_child_elim:                    0
% 7.58/1.49  inst_num_of_dismatching_blockings:      30
% 7.58/1.49  inst_num_of_non_proper_insts:           2570
% 7.58/1.49  inst_num_of_duplicates:                 0
% 7.58/1.49  inst_inst_num_from_inst_to_res:         0
% 7.58/1.49  inst_dismatching_checking_time:         0.
% 7.58/1.49  
% 7.58/1.49  ------ Resolution
% 7.58/1.49  
% 7.58/1.49  res_num_of_clauses:                     0
% 7.58/1.49  res_num_in_passive:                     0
% 7.58/1.49  res_num_in_active:                      0
% 7.58/1.49  res_num_of_loops:                       156
% 7.58/1.49  res_forward_subset_subsumed:            17
% 7.58/1.49  res_backward_subset_subsumed:           24
% 7.58/1.49  res_forward_subsumed:                   0
% 7.58/1.49  res_backward_subsumed:                  0
% 7.58/1.49  res_forward_subsumption_resolution:     0
% 7.58/1.49  res_backward_subsumption_resolution:    0
% 7.58/1.49  res_clause_to_clause_subsumption:       2277
% 7.58/1.49  res_orphan_elimination:                 0
% 7.58/1.49  res_tautology_del:                      5
% 7.58/1.49  res_num_eq_res_simplified:              0
% 7.58/1.49  res_num_sel_changes:                    0
% 7.58/1.49  res_moves_from_active_to_pass:          0
% 7.58/1.49  
% 7.58/1.49  ------ Superposition
% 7.58/1.49  
% 7.58/1.49  sup_time_total:                         0.
% 7.58/1.49  sup_time_generating:                    0.
% 7.58/1.49  sup_time_sim_full:                      0.
% 7.58/1.49  sup_time_sim_immed:                     0.
% 7.58/1.49  
% 7.58/1.49  sup_num_of_clauses:                     352
% 7.58/1.49  sup_num_in_active:                      66
% 7.58/1.49  sup_num_in_passive:                     286
% 7.58/1.49  sup_num_of_loops:                       124
% 7.58/1.49  sup_fw_superposition:                   340
% 7.58/1.49  sup_bw_superposition:                   286
% 7.58/1.49  sup_immediate_simplified:               179
% 7.58/1.49  sup_given_eliminated:                   1
% 7.58/1.49  comparisons_done:                       0
% 7.58/1.49  comparisons_avoided:                    6
% 7.58/1.49  
% 7.58/1.49  ------ Simplifications
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  sim_fw_subset_subsumed:                 55
% 7.58/1.49  sim_bw_subset_subsumed:                 13
% 7.58/1.49  sim_fw_subsumed:                        86
% 7.58/1.49  sim_bw_subsumed:                        3
% 7.58/1.49  sim_fw_subsumption_res:                 0
% 7.58/1.49  sim_bw_subsumption_res:                 0
% 7.58/1.49  sim_tautology_del:                      36
% 7.58/1.49  sim_eq_tautology_del:                   29
% 7.58/1.49  sim_eq_res_simp:                        3
% 7.58/1.49  sim_fw_demodulated:                     33
% 7.58/1.49  sim_bw_demodulated:                     55
% 7.58/1.49  sim_light_normalised:                   21
% 7.58/1.49  sim_joinable_taut:                      0
% 7.58/1.49  sim_joinable_simp:                      0
% 7.58/1.49  sim_ac_normalised:                      0
% 7.58/1.49  sim_smt_subsumption:                    0
% 7.58/1.49  
%------------------------------------------------------------------------------
