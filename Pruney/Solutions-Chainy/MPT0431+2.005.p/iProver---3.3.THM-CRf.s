%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:50 EST 2020

% Result     : Theorem 39.57s
% Output     : CNFRefutation 39.57s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 233 expanded)
%              Number of clauses        :   48 (  64 expanded)
%              Number of leaves         :   13 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  295 (1038 expanded)
%              Number of equality atoms :   64 (  92 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
           => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
     => ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,sK3),X0)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(X1,X0) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,X2),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
          & v3_setfam_1(X2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      & v3_setfam_1(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & v3_setfam_1(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & v3_setfam_1(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f25,f24])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_setfam_1(X1,X0)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    v3_setfam_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v3_setfam_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_124311,plain,
    ( k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))) = k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_943,plain,
    ( ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9397,plain,
    ( ~ r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),X0)) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_54057,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))))
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_9397])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_573,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1,X2)
    | X2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_2171,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
    | X0 != k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_6483,plain,
    ( r2_hidden(sK1,k4_xboole_0(X0,X1))
    | ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
    | k4_xboole_0(X0,X1) != k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_41450,plain,
    ( r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))))
    | ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
    | k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))) != k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_6483])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_447,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_448,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_449,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_985,plain,
    ( k3_tarski(k1_enumset1(X0,X0,sK3)) = k4_subset_1(k1_zfmisc_1(sK1),X0,sK3)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_449])).

cnf(c_1378,plain,
    ( k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3) = k3_tarski(k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_447,c_985])).

cnf(c_9,plain,
    ( v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,negated_conjecture,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X1,X0)
    | k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_165,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_164])).

cnf(c_446,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_166,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_477,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_478,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_914,plain,
    ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_17,c_19,c_166,c_478])).

cnf(c_1551,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1378,c_914])).

cnf(c_1554,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1551])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_490,plain,
    ( ~ r2_hidden(sK1,X0)
    | r2_hidden(sK1,k4_xboole_0(X0,sK3))
    | r2_hidden(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_608,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2))
    | r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
    | r2_hidden(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_505,plain,
    ( ~ r2_hidden(sK1,X0)
    | r2_hidden(sK1,k4_xboole_0(X0,sK2))
    | r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_576,plain,
    ( ~ r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3))
    | r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2))
    | r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_222,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_237,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_10,plain,
    ( ~ v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( v3_setfam_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_186,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_13,negated_conjecture,
    ( v3_setfam_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0)
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_175,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ r2_hidden(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124311,c_54057,c_41450,c_1554,c_608,c_576,c_477,c_237,c_186,c_175,c_165,c_12,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:30:09 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 39.57/5.46  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.57/5.46  
% 39.57/5.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.57/5.46  
% 39.57/5.46  ------  iProver source info
% 39.57/5.46  
% 39.57/5.46  git: date: 2020-06-30 10:37:57 +0100
% 39.57/5.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.57/5.46  git: non_committed_changes: false
% 39.57/5.46  git: last_make_outside_of_git: false
% 39.57/5.46  
% 39.57/5.46  ------ 
% 39.57/5.46  
% 39.57/5.46  ------ Input Options
% 39.57/5.46  
% 39.57/5.46  --out_options                           all
% 39.57/5.46  --tptp_safe_out                         true
% 39.57/5.46  --problem_path                          ""
% 39.57/5.46  --include_path                          ""
% 39.57/5.46  --clausifier                            res/vclausify_rel
% 39.57/5.46  --clausifier_options                    ""
% 39.57/5.46  --stdin                                 false
% 39.57/5.46  --stats_out                             all
% 39.57/5.46  
% 39.57/5.46  ------ General Options
% 39.57/5.46  
% 39.57/5.46  --fof                                   false
% 39.57/5.46  --time_out_real                         305.
% 39.57/5.46  --time_out_virtual                      -1.
% 39.57/5.46  --symbol_type_check                     false
% 39.57/5.46  --clausify_out                          false
% 39.57/5.46  --sig_cnt_out                           false
% 39.57/5.46  --trig_cnt_out                          false
% 39.57/5.46  --trig_cnt_out_tolerance                1.
% 39.57/5.46  --trig_cnt_out_sk_spl                   false
% 39.57/5.46  --abstr_cl_out                          false
% 39.57/5.46  
% 39.57/5.46  ------ Global Options
% 39.57/5.46  
% 39.57/5.46  --schedule                              default
% 39.57/5.46  --add_important_lit                     false
% 39.57/5.46  --prop_solver_per_cl                    1000
% 39.57/5.46  --min_unsat_core                        false
% 39.57/5.46  --soft_assumptions                      false
% 39.57/5.46  --soft_lemma_size                       3
% 39.57/5.46  --prop_impl_unit_size                   0
% 39.57/5.46  --prop_impl_unit                        []
% 39.57/5.46  --share_sel_clauses                     true
% 39.57/5.46  --reset_solvers                         false
% 39.57/5.46  --bc_imp_inh                            [conj_cone]
% 39.57/5.46  --conj_cone_tolerance                   3.
% 39.57/5.46  --extra_neg_conj                        none
% 39.57/5.46  --large_theory_mode                     true
% 39.57/5.46  --prolific_symb_bound                   200
% 39.57/5.46  --lt_threshold                          2000
% 39.57/5.46  --clause_weak_htbl                      true
% 39.57/5.46  --gc_record_bc_elim                     false
% 39.57/5.46  
% 39.57/5.46  ------ Preprocessing Options
% 39.57/5.46  
% 39.57/5.46  --preprocessing_flag                    true
% 39.57/5.46  --time_out_prep_mult                    0.1
% 39.57/5.46  --splitting_mode                        input
% 39.57/5.46  --splitting_grd                         true
% 39.57/5.46  --splitting_cvd                         false
% 39.57/5.46  --splitting_cvd_svl                     false
% 39.57/5.46  --splitting_nvd                         32
% 39.57/5.46  --sub_typing                            true
% 39.57/5.46  --prep_gs_sim                           true
% 39.57/5.46  --prep_unflatten                        true
% 39.57/5.46  --prep_res_sim                          true
% 39.57/5.46  --prep_upred                            true
% 39.57/5.46  --prep_sem_filter                       exhaustive
% 39.57/5.46  --prep_sem_filter_out                   false
% 39.57/5.46  --pred_elim                             true
% 39.57/5.46  --res_sim_input                         true
% 39.57/5.46  --eq_ax_congr_red                       true
% 39.57/5.46  --pure_diseq_elim                       true
% 39.57/5.46  --brand_transform                       false
% 39.57/5.46  --non_eq_to_eq                          false
% 39.57/5.46  --prep_def_merge                        true
% 39.57/5.46  --prep_def_merge_prop_impl              false
% 39.57/5.46  --prep_def_merge_mbd                    true
% 39.57/5.46  --prep_def_merge_tr_red                 false
% 39.57/5.46  --prep_def_merge_tr_cl                  false
% 39.57/5.46  --smt_preprocessing                     true
% 39.57/5.46  --smt_ac_axioms                         fast
% 39.57/5.46  --preprocessed_out                      false
% 39.57/5.46  --preprocessed_stats                    false
% 39.57/5.46  
% 39.57/5.46  ------ Abstraction refinement Options
% 39.57/5.46  
% 39.57/5.46  --abstr_ref                             []
% 39.57/5.46  --abstr_ref_prep                        false
% 39.57/5.46  --abstr_ref_until_sat                   false
% 39.57/5.46  --abstr_ref_sig_restrict                funpre
% 39.57/5.46  --abstr_ref_af_restrict_to_split_sk     false
% 39.57/5.46  --abstr_ref_under                       []
% 39.57/5.46  
% 39.57/5.46  ------ SAT Options
% 39.57/5.46  
% 39.57/5.46  --sat_mode                              false
% 39.57/5.46  --sat_fm_restart_options                ""
% 39.57/5.46  --sat_gr_def                            false
% 39.57/5.46  --sat_epr_types                         true
% 39.57/5.46  --sat_non_cyclic_types                  false
% 39.57/5.46  --sat_finite_models                     false
% 39.57/5.46  --sat_fm_lemmas                         false
% 39.57/5.46  --sat_fm_prep                           false
% 39.57/5.46  --sat_fm_uc_incr                        true
% 39.57/5.46  --sat_out_model                         small
% 39.57/5.46  --sat_out_clauses                       false
% 39.57/5.46  
% 39.57/5.46  ------ QBF Options
% 39.57/5.46  
% 39.57/5.46  --qbf_mode                              false
% 39.57/5.46  --qbf_elim_univ                         false
% 39.57/5.46  --qbf_dom_inst                          none
% 39.57/5.46  --qbf_dom_pre_inst                      false
% 39.57/5.46  --qbf_sk_in                             false
% 39.57/5.46  --qbf_pred_elim                         true
% 39.57/5.46  --qbf_split                             512
% 39.57/5.46  
% 39.57/5.46  ------ BMC1 Options
% 39.57/5.46  
% 39.57/5.46  --bmc1_incremental                      false
% 39.57/5.46  --bmc1_axioms                           reachable_all
% 39.57/5.46  --bmc1_min_bound                        0
% 39.57/5.46  --bmc1_max_bound                        -1
% 39.57/5.46  --bmc1_max_bound_default                -1
% 39.57/5.46  --bmc1_symbol_reachability              true
% 39.57/5.46  --bmc1_property_lemmas                  false
% 39.57/5.46  --bmc1_k_induction                      false
% 39.57/5.46  --bmc1_non_equiv_states                 false
% 39.57/5.46  --bmc1_deadlock                         false
% 39.57/5.46  --bmc1_ucm                              false
% 39.57/5.46  --bmc1_add_unsat_core                   none
% 39.57/5.46  --bmc1_unsat_core_children              false
% 39.57/5.46  --bmc1_unsat_core_extrapolate_axioms    false
% 39.57/5.46  --bmc1_out_stat                         full
% 39.57/5.46  --bmc1_ground_init                      false
% 39.57/5.46  --bmc1_pre_inst_next_state              false
% 39.57/5.46  --bmc1_pre_inst_state                   false
% 39.57/5.46  --bmc1_pre_inst_reach_state             false
% 39.57/5.46  --bmc1_out_unsat_core                   false
% 39.57/5.46  --bmc1_aig_witness_out                  false
% 39.57/5.46  --bmc1_verbose                          false
% 39.57/5.46  --bmc1_dump_clauses_tptp                false
% 39.57/5.46  --bmc1_dump_unsat_core_tptp             false
% 39.57/5.46  --bmc1_dump_file                        -
% 39.57/5.46  --bmc1_ucm_expand_uc_limit              128
% 39.57/5.46  --bmc1_ucm_n_expand_iterations          6
% 39.57/5.46  --bmc1_ucm_extend_mode                  1
% 39.57/5.46  --bmc1_ucm_init_mode                    2
% 39.57/5.46  --bmc1_ucm_cone_mode                    none
% 39.57/5.46  --bmc1_ucm_reduced_relation_type        0
% 39.57/5.46  --bmc1_ucm_relax_model                  4
% 39.57/5.46  --bmc1_ucm_full_tr_after_sat            true
% 39.57/5.46  --bmc1_ucm_expand_neg_assumptions       false
% 39.57/5.46  --bmc1_ucm_layered_model                none
% 39.57/5.46  --bmc1_ucm_max_lemma_size               10
% 39.57/5.46  
% 39.57/5.46  ------ AIG Options
% 39.57/5.46  
% 39.57/5.46  --aig_mode                              false
% 39.57/5.46  
% 39.57/5.46  ------ Instantiation Options
% 39.57/5.46  
% 39.57/5.46  --instantiation_flag                    true
% 39.57/5.46  --inst_sos_flag                         true
% 39.57/5.46  --inst_sos_phase                        true
% 39.57/5.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.57/5.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.57/5.46  --inst_lit_sel_side                     num_symb
% 39.57/5.46  --inst_solver_per_active                1400
% 39.57/5.46  --inst_solver_calls_frac                1.
% 39.57/5.46  --inst_passive_queue_type               priority_queues
% 39.57/5.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.57/5.46  --inst_passive_queues_freq              [25;2]
% 39.57/5.46  --inst_dismatching                      true
% 39.57/5.46  --inst_eager_unprocessed_to_passive     true
% 39.57/5.46  --inst_prop_sim_given                   true
% 39.57/5.46  --inst_prop_sim_new                     false
% 39.57/5.46  --inst_subs_new                         false
% 39.57/5.46  --inst_eq_res_simp                      false
% 39.57/5.46  --inst_subs_given                       false
% 39.57/5.46  --inst_orphan_elimination               true
% 39.57/5.46  --inst_learning_loop_flag               true
% 39.57/5.46  --inst_learning_start                   3000
% 39.57/5.46  --inst_learning_factor                  2
% 39.57/5.46  --inst_start_prop_sim_after_learn       3
% 39.57/5.46  --inst_sel_renew                        solver
% 39.57/5.46  --inst_lit_activity_flag                true
% 39.57/5.46  --inst_restr_to_given                   false
% 39.57/5.46  --inst_activity_threshold               500
% 39.57/5.46  --inst_out_proof                        true
% 39.57/5.46  
% 39.57/5.46  ------ Resolution Options
% 39.57/5.46  
% 39.57/5.46  --resolution_flag                       true
% 39.57/5.46  --res_lit_sel                           adaptive
% 39.57/5.46  --res_lit_sel_side                      none
% 39.57/5.46  --res_ordering                          kbo
% 39.57/5.46  --res_to_prop_solver                    active
% 39.57/5.46  --res_prop_simpl_new                    false
% 39.57/5.46  --res_prop_simpl_given                  true
% 39.57/5.46  --res_passive_queue_type                priority_queues
% 39.57/5.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.57/5.46  --res_passive_queues_freq               [15;5]
% 39.57/5.46  --res_forward_subs                      full
% 39.57/5.46  --res_backward_subs                     full
% 39.57/5.46  --res_forward_subs_resolution           true
% 39.57/5.46  --res_backward_subs_resolution          true
% 39.57/5.46  --res_orphan_elimination                true
% 39.57/5.46  --res_time_limit                        2.
% 39.57/5.46  --res_out_proof                         true
% 39.57/5.46  
% 39.57/5.46  ------ Superposition Options
% 39.57/5.46  
% 39.57/5.46  --superposition_flag                    true
% 39.57/5.46  --sup_passive_queue_type                priority_queues
% 39.57/5.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.57/5.46  --sup_passive_queues_freq               [8;1;4]
% 39.57/5.46  --demod_completeness_check              fast
% 39.57/5.46  --demod_use_ground                      true
% 39.57/5.46  --sup_to_prop_solver                    passive
% 39.57/5.46  --sup_prop_simpl_new                    true
% 39.57/5.46  --sup_prop_simpl_given                  true
% 39.57/5.46  --sup_fun_splitting                     true
% 39.57/5.46  --sup_smt_interval                      50000
% 39.57/5.46  
% 39.57/5.46  ------ Superposition Simplification Setup
% 39.57/5.46  
% 39.57/5.46  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.57/5.46  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.57/5.46  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.57/5.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.57/5.46  --sup_full_triv                         [TrivRules;PropSubs]
% 39.57/5.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.57/5.46  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.57/5.46  --sup_immed_triv                        [TrivRules]
% 39.57/5.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.57/5.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.57/5.46  --sup_immed_bw_main                     []
% 39.57/5.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.57/5.46  --sup_input_triv                        [Unflattening;TrivRules]
% 39.57/5.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.57/5.46  --sup_input_bw                          []
% 39.57/5.46  
% 39.57/5.46  ------ Combination Options
% 39.57/5.46  
% 39.57/5.46  --comb_res_mult                         3
% 39.57/5.46  --comb_sup_mult                         2
% 39.57/5.46  --comb_inst_mult                        10
% 39.57/5.46  
% 39.57/5.46  ------ Debug Options
% 39.57/5.46  
% 39.57/5.46  --dbg_backtrace                         false
% 39.57/5.46  --dbg_dump_prop_clauses                 false
% 39.57/5.46  --dbg_dump_prop_clauses_file            -
% 39.57/5.46  --dbg_out_stat                          false
% 39.57/5.46  ------ Parsing...
% 39.57/5.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.57/5.46  
% 39.57/5.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 39.57/5.46  
% 39.57/5.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.57/5.46  
% 39.57/5.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.57/5.46  ------ Proving...
% 39.57/5.46  ------ Problem Properties 
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  clauses                                 16
% 39.57/5.46  conjectures                             2
% 39.57/5.46  EPR                                     2
% 39.57/5.46  Horn                                    12
% 39.57/5.46  unary                                   5
% 39.57/5.46  binary                                  5
% 39.57/5.46  lits                                    34
% 39.57/5.46  lits eq                                 9
% 39.57/5.46  fd_pure                                 0
% 39.57/5.46  fd_pseudo                               0
% 39.57/5.46  fd_cond                                 0
% 39.57/5.46  fd_pseudo_cond                          3
% 39.57/5.46  AC symbols                              0
% 39.57/5.46  
% 39.57/5.46  ------ Schedule dynamic 5 is on 
% 39.57/5.46  
% 39.57/5.46  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  ------ 
% 39.57/5.46  Current options:
% 39.57/5.46  ------ 
% 39.57/5.46  
% 39.57/5.46  ------ Input Options
% 39.57/5.46  
% 39.57/5.46  --out_options                           all
% 39.57/5.46  --tptp_safe_out                         true
% 39.57/5.46  --problem_path                          ""
% 39.57/5.46  --include_path                          ""
% 39.57/5.46  --clausifier                            res/vclausify_rel
% 39.57/5.46  --clausifier_options                    ""
% 39.57/5.46  --stdin                                 false
% 39.57/5.46  --stats_out                             all
% 39.57/5.46  
% 39.57/5.46  ------ General Options
% 39.57/5.46  
% 39.57/5.46  --fof                                   false
% 39.57/5.46  --time_out_real                         305.
% 39.57/5.46  --time_out_virtual                      -1.
% 39.57/5.46  --symbol_type_check                     false
% 39.57/5.46  --clausify_out                          false
% 39.57/5.46  --sig_cnt_out                           false
% 39.57/5.46  --trig_cnt_out                          false
% 39.57/5.46  --trig_cnt_out_tolerance                1.
% 39.57/5.46  --trig_cnt_out_sk_spl                   false
% 39.57/5.46  --abstr_cl_out                          false
% 39.57/5.46  
% 39.57/5.46  ------ Global Options
% 39.57/5.46  
% 39.57/5.46  --schedule                              default
% 39.57/5.46  --add_important_lit                     false
% 39.57/5.46  --prop_solver_per_cl                    1000
% 39.57/5.46  --min_unsat_core                        false
% 39.57/5.46  --soft_assumptions                      false
% 39.57/5.46  --soft_lemma_size                       3
% 39.57/5.46  --prop_impl_unit_size                   0
% 39.57/5.46  --prop_impl_unit                        []
% 39.57/5.46  --share_sel_clauses                     true
% 39.57/5.46  --reset_solvers                         false
% 39.57/5.46  --bc_imp_inh                            [conj_cone]
% 39.57/5.46  --conj_cone_tolerance                   3.
% 39.57/5.46  --extra_neg_conj                        none
% 39.57/5.46  --large_theory_mode                     true
% 39.57/5.46  --prolific_symb_bound                   200
% 39.57/5.46  --lt_threshold                          2000
% 39.57/5.46  --clause_weak_htbl                      true
% 39.57/5.46  --gc_record_bc_elim                     false
% 39.57/5.46  
% 39.57/5.46  ------ Preprocessing Options
% 39.57/5.46  
% 39.57/5.46  --preprocessing_flag                    true
% 39.57/5.46  --time_out_prep_mult                    0.1
% 39.57/5.46  --splitting_mode                        input
% 39.57/5.46  --splitting_grd                         true
% 39.57/5.46  --splitting_cvd                         false
% 39.57/5.46  --splitting_cvd_svl                     false
% 39.57/5.46  --splitting_nvd                         32
% 39.57/5.46  --sub_typing                            true
% 39.57/5.46  --prep_gs_sim                           true
% 39.57/5.46  --prep_unflatten                        true
% 39.57/5.46  --prep_res_sim                          true
% 39.57/5.46  --prep_upred                            true
% 39.57/5.46  --prep_sem_filter                       exhaustive
% 39.57/5.46  --prep_sem_filter_out                   false
% 39.57/5.46  --pred_elim                             true
% 39.57/5.46  --res_sim_input                         true
% 39.57/5.46  --eq_ax_congr_red                       true
% 39.57/5.46  --pure_diseq_elim                       true
% 39.57/5.46  --brand_transform                       false
% 39.57/5.46  --non_eq_to_eq                          false
% 39.57/5.46  --prep_def_merge                        true
% 39.57/5.46  --prep_def_merge_prop_impl              false
% 39.57/5.46  --prep_def_merge_mbd                    true
% 39.57/5.46  --prep_def_merge_tr_red                 false
% 39.57/5.46  --prep_def_merge_tr_cl                  false
% 39.57/5.46  --smt_preprocessing                     true
% 39.57/5.46  --smt_ac_axioms                         fast
% 39.57/5.46  --preprocessed_out                      false
% 39.57/5.46  --preprocessed_stats                    false
% 39.57/5.46  
% 39.57/5.46  ------ Abstraction refinement Options
% 39.57/5.46  
% 39.57/5.46  --abstr_ref                             []
% 39.57/5.46  --abstr_ref_prep                        false
% 39.57/5.46  --abstr_ref_until_sat                   false
% 39.57/5.46  --abstr_ref_sig_restrict                funpre
% 39.57/5.46  --abstr_ref_af_restrict_to_split_sk     false
% 39.57/5.46  --abstr_ref_under                       []
% 39.57/5.46  
% 39.57/5.46  ------ SAT Options
% 39.57/5.46  
% 39.57/5.46  --sat_mode                              false
% 39.57/5.46  --sat_fm_restart_options                ""
% 39.57/5.46  --sat_gr_def                            false
% 39.57/5.46  --sat_epr_types                         true
% 39.57/5.46  --sat_non_cyclic_types                  false
% 39.57/5.46  --sat_finite_models                     false
% 39.57/5.46  --sat_fm_lemmas                         false
% 39.57/5.46  --sat_fm_prep                           false
% 39.57/5.46  --sat_fm_uc_incr                        true
% 39.57/5.46  --sat_out_model                         small
% 39.57/5.46  --sat_out_clauses                       false
% 39.57/5.46  
% 39.57/5.46  ------ QBF Options
% 39.57/5.46  
% 39.57/5.46  --qbf_mode                              false
% 39.57/5.46  --qbf_elim_univ                         false
% 39.57/5.46  --qbf_dom_inst                          none
% 39.57/5.46  --qbf_dom_pre_inst                      false
% 39.57/5.46  --qbf_sk_in                             false
% 39.57/5.46  --qbf_pred_elim                         true
% 39.57/5.46  --qbf_split                             512
% 39.57/5.46  
% 39.57/5.46  ------ BMC1 Options
% 39.57/5.46  
% 39.57/5.46  --bmc1_incremental                      false
% 39.57/5.46  --bmc1_axioms                           reachable_all
% 39.57/5.46  --bmc1_min_bound                        0
% 39.57/5.46  --bmc1_max_bound                        -1
% 39.57/5.46  --bmc1_max_bound_default                -1
% 39.57/5.46  --bmc1_symbol_reachability              true
% 39.57/5.46  --bmc1_property_lemmas                  false
% 39.57/5.46  --bmc1_k_induction                      false
% 39.57/5.46  --bmc1_non_equiv_states                 false
% 39.57/5.46  --bmc1_deadlock                         false
% 39.57/5.46  --bmc1_ucm                              false
% 39.57/5.46  --bmc1_add_unsat_core                   none
% 39.57/5.46  --bmc1_unsat_core_children              false
% 39.57/5.46  --bmc1_unsat_core_extrapolate_axioms    false
% 39.57/5.46  --bmc1_out_stat                         full
% 39.57/5.46  --bmc1_ground_init                      false
% 39.57/5.46  --bmc1_pre_inst_next_state              false
% 39.57/5.46  --bmc1_pre_inst_state                   false
% 39.57/5.46  --bmc1_pre_inst_reach_state             false
% 39.57/5.46  --bmc1_out_unsat_core                   false
% 39.57/5.46  --bmc1_aig_witness_out                  false
% 39.57/5.46  --bmc1_verbose                          false
% 39.57/5.46  --bmc1_dump_clauses_tptp                false
% 39.57/5.46  --bmc1_dump_unsat_core_tptp             false
% 39.57/5.46  --bmc1_dump_file                        -
% 39.57/5.46  --bmc1_ucm_expand_uc_limit              128
% 39.57/5.46  --bmc1_ucm_n_expand_iterations          6
% 39.57/5.46  --bmc1_ucm_extend_mode                  1
% 39.57/5.46  --bmc1_ucm_init_mode                    2
% 39.57/5.46  --bmc1_ucm_cone_mode                    none
% 39.57/5.46  --bmc1_ucm_reduced_relation_type        0
% 39.57/5.46  --bmc1_ucm_relax_model                  4
% 39.57/5.46  --bmc1_ucm_full_tr_after_sat            true
% 39.57/5.46  --bmc1_ucm_expand_neg_assumptions       false
% 39.57/5.46  --bmc1_ucm_layered_model                none
% 39.57/5.46  --bmc1_ucm_max_lemma_size               10
% 39.57/5.46  
% 39.57/5.46  ------ AIG Options
% 39.57/5.46  
% 39.57/5.46  --aig_mode                              false
% 39.57/5.46  
% 39.57/5.46  ------ Instantiation Options
% 39.57/5.46  
% 39.57/5.46  --instantiation_flag                    true
% 39.57/5.46  --inst_sos_flag                         true
% 39.57/5.46  --inst_sos_phase                        true
% 39.57/5.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.57/5.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.57/5.46  --inst_lit_sel_side                     none
% 39.57/5.46  --inst_solver_per_active                1400
% 39.57/5.46  --inst_solver_calls_frac                1.
% 39.57/5.46  --inst_passive_queue_type               priority_queues
% 39.57/5.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.57/5.46  --inst_passive_queues_freq              [25;2]
% 39.57/5.46  --inst_dismatching                      true
% 39.57/5.46  --inst_eager_unprocessed_to_passive     true
% 39.57/5.46  --inst_prop_sim_given                   true
% 39.57/5.46  --inst_prop_sim_new                     false
% 39.57/5.46  --inst_subs_new                         false
% 39.57/5.46  --inst_eq_res_simp                      false
% 39.57/5.46  --inst_subs_given                       false
% 39.57/5.46  --inst_orphan_elimination               true
% 39.57/5.46  --inst_learning_loop_flag               true
% 39.57/5.46  --inst_learning_start                   3000
% 39.57/5.46  --inst_learning_factor                  2
% 39.57/5.46  --inst_start_prop_sim_after_learn       3
% 39.57/5.46  --inst_sel_renew                        solver
% 39.57/5.46  --inst_lit_activity_flag                true
% 39.57/5.46  --inst_restr_to_given                   false
% 39.57/5.46  --inst_activity_threshold               500
% 39.57/5.46  --inst_out_proof                        true
% 39.57/5.46  
% 39.57/5.46  ------ Resolution Options
% 39.57/5.46  
% 39.57/5.46  --resolution_flag                       false
% 39.57/5.46  --res_lit_sel                           adaptive
% 39.57/5.46  --res_lit_sel_side                      none
% 39.57/5.46  --res_ordering                          kbo
% 39.57/5.46  --res_to_prop_solver                    active
% 39.57/5.46  --res_prop_simpl_new                    false
% 39.57/5.46  --res_prop_simpl_given                  true
% 39.57/5.46  --res_passive_queue_type                priority_queues
% 39.57/5.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.57/5.46  --res_passive_queues_freq               [15;5]
% 39.57/5.46  --res_forward_subs                      full
% 39.57/5.46  --res_backward_subs                     full
% 39.57/5.46  --res_forward_subs_resolution           true
% 39.57/5.46  --res_backward_subs_resolution          true
% 39.57/5.46  --res_orphan_elimination                true
% 39.57/5.46  --res_time_limit                        2.
% 39.57/5.46  --res_out_proof                         true
% 39.57/5.46  
% 39.57/5.46  ------ Superposition Options
% 39.57/5.46  
% 39.57/5.46  --superposition_flag                    true
% 39.57/5.46  --sup_passive_queue_type                priority_queues
% 39.57/5.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.57/5.46  --sup_passive_queues_freq               [8;1;4]
% 39.57/5.46  --demod_completeness_check              fast
% 39.57/5.46  --demod_use_ground                      true
% 39.57/5.46  --sup_to_prop_solver                    passive
% 39.57/5.46  --sup_prop_simpl_new                    true
% 39.57/5.46  --sup_prop_simpl_given                  true
% 39.57/5.46  --sup_fun_splitting                     true
% 39.57/5.46  --sup_smt_interval                      50000
% 39.57/5.46  
% 39.57/5.46  ------ Superposition Simplification Setup
% 39.57/5.46  
% 39.57/5.46  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.57/5.46  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.57/5.46  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.57/5.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.57/5.46  --sup_full_triv                         [TrivRules;PropSubs]
% 39.57/5.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.57/5.46  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.57/5.46  --sup_immed_triv                        [TrivRules]
% 39.57/5.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.57/5.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.57/5.46  --sup_immed_bw_main                     []
% 39.57/5.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.57/5.46  --sup_input_triv                        [Unflattening;TrivRules]
% 39.57/5.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.57/5.46  --sup_input_bw                          []
% 39.57/5.46  
% 39.57/5.46  ------ Combination Options
% 39.57/5.46  
% 39.57/5.46  --comb_res_mult                         3
% 39.57/5.46  --comb_sup_mult                         2
% 39.57/5.46  --comb_inst_mult                        10
% 39.57/5.46  
% 39.57/5.46  ------ Debug Options
% 39.57/5.46  
% 39.57/5.46  --dbg_backtrace                         false
% 39.57/5.46  --dbg_dump_prop_clauses                 false
% 39.57/5.46  --dbg_dump_prop_clauses_file            -
% 39.57/5.46  --dbg_out_stat                          false
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  ------ Proving...
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  % SZS status Theorem for theBenchmark.p
% 39.57/5.46  
% 39.57/5.46  % SZS output start CNFRefutation for theBenchmark.p
% 39.57/5.46  
% 39.57/5.46  fof(f2,axiom,(
% 39.57/5.46    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f33,plain,(
% 39.57/5.46    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 39.57/5.46    inference(cnf_transformation,[],[f2])).
% 39.57/5.46  
% 39.57/5.46  fof(f4,axiom,(
% 39.57/5.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f35,plain,(
% 39.57/5.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.57/5.46    inference(cnf_transformation,[],[f4])).
% 39.57/5.46  
% 39.57/5.46  fof(f3,axiom,(
% 39.57/5.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f34,plain,(
% 39.57/5.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 39.57/5.46    inference(cnf_transformation,[],[f3])).
% 39.57/5.46  
% 39.57/5.46  fof(f45,plain,(
% 39.57/5.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 39.57/5.46    inference(definition_unfolding,[],[f35,f34])).
% 39.57/5.46  
% 39.57/5.46  fof(f46,plain,(
% 39.57/5.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 39.57/5.46    inference(definition_unfolding,[],[f33,f45])).
% 39.57/5.46  
% 39.57/5.46  fof(f1,axiom,(
% 39.57/5.46    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f18,plain,(
% 39.57/5.46    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.57/5.46    inference(nnf_transformation,[],[f1])).
% 39.57/5.46  
% 39.57/5.46  fof(f19,plain,(
% 39.57/5.46    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.57/5.46    inference(flattening,[],[f18])).
% 39.57/5.46  
% 39.57/5.46  fof(f20,plain,(
% 39.57/5.46    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.57/5.46    inference(rectify,[],[f19])).
% 39.57/5.46  
% 39.57/5.46  fof(f21,plain,(
% 39.57/5.46    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 39.57/5.46    introduced(choice_axiom,[])).
% 39.57/5.46  
% 39.57/5.46  fof(f22,plain,(
% 39.57/5.46    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.57/5.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 39.57/5.46  
% 39.57/5.46  fof(f28,plain,(
% 39.57/5.46    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 39.57/5.46    inference(cnf_transformation,[],[f22])).
% 39.57/5.46  
% 39.57/5.46  fof(f49,plain,(
% 39.57/5.46    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 39.57/5.46    inference(equality_resolution,[],[f28])).
% 39.57/5.46  
% 39.57/5.46  fof(f8,conjecture,(
% 39.57/5.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f9,negated_conjecture,(
% 39.57/5.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 39.57/5.46    inference(negated_conjecture,[],[f8])).
% 39.57/5.46  
% 39.57/5.46  fof(f10,plain,(
% 39.57/5.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)))),
% 39.57/5.46    inference(pure_predicate_removal,[],[f9])).
% 39.57/5.46  
% 39.57/5.46  fof(f16,plain,(
% 39.57/5.46    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)))),
% 39.57/5.46    inference(ennf_transformation,[],[f10])).
% 39.57/5.46  
% 39.57/5.46  fof(f17,plain,(
% 39.57/5.46    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))),
% 39.57/5.46    inference(flattening,[],[f16])).
% 39.57/5.46  
% 39.57/5.46  fof(f25,plain,(
% 39.57/5.46    ( ! [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,sK3),X0) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(sK3,X0))) )),
% 39.57/5.46    introduced(choice_axiom,[])).
% 39.57/5.46  
% 39.57/5.46  fof(f24,plain,(
% 39.57/5.46    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(sK2,sK1))),
% 39.57/5.46    introduced(choice_axiom,[])).
% 39.57/5.46  
% 39.57/5.46  fof(f26,plain,(
% 39.57/5.46    (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(sK3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) & v3_setfam_1(sK2,sK1)),
% 39.57/5.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f25,f24])).
% 39.57/5.46  
% 39.57/5.46  fof(f41,plain,(
% 39.57/5.46    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 39.57/5.46    inference(cnf_transformation,[],[f26])).
% 39.57/5.46  
% 39.57/5.46  fof(f43,plain,(
% 39.57/5.46    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 39.57/5.46    inference(cnf_transformation,[],[f26])).
% 39.57/5.46  
% 39.57/5.46  fof(f6,axiom,(
% 39.57/5.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f13,plain,(
% 39.57/5.46    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.57/5.46    inference(ennf_transformation,[],[f6])).
% 39.57/5.46  
% 39.57/5.46  fof(f14,plain,(
% 39.57/5.46    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.57/5.46    inference(flattening,[],[f13])).
% 39.57/5.46  
% 39.57/5.46  fof(f37,plain,(
% 39.57/5.46    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.57/5.46    inference(cnf_transformation,[],[f14])).
% 39.57/5.46  
% 39.57/5.46  fof(f47,plain,(
% 39.57/5.46    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.57/5.46    inference(definition_unfolding,[],[f37,f45])).
% 39.57/5.46  
% 39.57/5.46  fof(f7,axiom,(
% 39.57/5.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f15,plain,(
% 39.57/5.46    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 39.57/5.46    inference(ennf_transformation,[],[f7])).
% 39.57/5.46  
% 39.57/5.46  fof(f23,plain,(
% 39.57/5.46    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 39.57/5.46    inference(nnf_transformation,[],[f15])).
% 39.57/5.46  
% 39.57/5.46  fof(f39,plain,(
% 39.57/5.46    ( ! [X0,X1] : (v3_setfam_1(X1,X0) | r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 39.57/5.46    inference(cnf_transformation,[],[f23])).
% 39.57/5.46  
% 39.57/5.46  fof(f44,plain,(
% 39.57/5.46    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1)),
% 39.57/5.46    inference(cnf_transformation,[],[f26])).
% 39.57/5.46  
% 39.57/5.46  fof(f5,axiom,(
% 39.57/5.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 39.57/5.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.57/5.46  
% 39.57/5.46  fof(f11,plain,(
% 39.57/5.46    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.57/5.46    inference(ennf_transformation,[],[f5])).
% 39.57/5.46  
% 39.57/5.46  fof(f12,plain,(
% 39.57/5.46    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.57/5.46    inference(flattening,[],[f11])).
% 39.57/5.46  
% 39.57/5.46  fof(f36,plain,(
% 39.57/5.46    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.57/5.46    inference(cnf_transformation,[],[f12])).
% 39.57/5.46  
% 39.57/5.46  fof(f29,plain,(
% 39.57/5.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 39.57/5.46    inference(cnf_transformation,[],[f22])).
% 39.57/5.46  
% 39.57/5.46  fof(f48,plain,(
% 39.57/5.46    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 39.57/5.46    inference(equality_resolution,[],[f29])).
% 39.57/5.46  
% 39.57/5.46  fof(f38,plain,(
% 39.57/5.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 39.57/5.46    inference(cnf_transformation,[],[f23])).
% 39.57/5.46  
% 39.57/5.46  fof(f40,plain,(
% 39.57/5.46    v3_setfam_1(sK2,sK1)),
% 39.57/5.46    inference(cnf_transformation,[],[f26])).
% 39.57/5.46  
% 39.57/5.46  fof(f42,plain,(
% 39.57/5.46    v3_setfam_1(sK3,sK1)),
% 39.57/5.46    inference(cnf_transformation,[],[f26])).
% 39.57/5.46  
% 39.57/5.46  cnf(c_6,plain,
% 39.57/5.46      ( k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 39.57/5.46      inference(cnf_transformation,[],[f46]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_124311,plain,
% 39.57/5.46      ( k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))) = k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_6]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_4,plain,
% 39.57/5.46      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 39.57/5.46      inference(cnf_transformation,[],[f49]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_943,plain,
% 39.57/5.46      ( ~ r2_hidden(sK1,X0) | ~ r2_hidden(sK1,k4_xboole_0(X1,X0)) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_4]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_9397,plain,
% 39.57/5.46      ( ~ r2_hidden(sK1,X0)
% 39.57/5.46      | ~ r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),X0)) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_943]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_54057,plain,
% 39.57/5.46      ( ~ r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))))
% 39.57/5.46      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,sK3))) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_9397]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_225,plain,
% 39.57/5.46      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.57/5.46      theory(equality) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_573,plain,
% 39.57/5.46      ( ~ r2_hidden(X0,X1) | r2_hidden(sK1,X2) | X2 != X1 | sK1 != X0 ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_225]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_2171,plain,
% 39.57/5.46      ( r2_hidden(sK1,X0)
% 39.57/5.46      | ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
% 39.57/5.46      | X0 != k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3)
% 39.57/5.46      | sK1 != sK1 ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_573]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_6483,plain,
% 39.57/5.46      ( r2_hidden(sK1,k4_xboole_0(X0,X1))
% 39.57/5.46      | ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
% 39.57/5.46      | k4_xboole_0(X0,X1) != k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3)
% 39.57/5.46      | sK1 != sK1 ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_2171]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_41450,plain,
% 39.57/5.46      ( r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))))
% 39.57/5.46      | ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
% 39.57/5.46      | k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k3_tarski(k1_enumset1(sK2,sK2,sK3))) != k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3)
% 39.57/5.46      | sK1 != sK1 ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_6483]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_14,negated_conjecture,
% 39.57/5.46      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 39.57/5.46      inference(cnf_transformation,[],[f41]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_447,plain,
% 39.57/5.46      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_12,negated_conjecture,
% 39.57/5.46      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 39.57/5.46      inference(cnf_transformation,[],[f43]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_448,plain,
% 39.57/5.46      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_8,plain,
% 39.57/5.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.57/5.46      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.57/5.46      | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 39.57/5.46      inference(cnf_transformation,[],[f47]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_449,plain,
% 39.57/5.46      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 39.57/5.46      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 39.57/5.46      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_985,plain,
% 39.57/5.46      ( k3_tarski(k1_enumset1(X0,X0,sK3)) = k4_subset_1(k1_zfmisc_1(sK1),X0,sK3)
% 39.57/5.46      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 39.57/5.46      inference(superposition,[status(thm)],[c_448,c_449]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_1378,plain,
% 39.57/5.46      ( k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3) = k3_tarski(k1_enumset1(sK2,sK2,sK3)) ),
% 39.57/5.46      inference(superposition,[status(thm)],[c_447,c_985]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_9,plain,
% 39.57/5.46      ( v3_setfam_1(X0,X1)
% 39.57/5.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 39.57/5.46      | r2_hidden(X1,X0) ),
% 39.57/5.46      inference(cnf_transformation,[],[f39]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_11,negated_conjecture,
% 39.57/5.46      ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK1) ),
% 39.57/5.46      inference(cnf_transformation,[],[f44]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_164,plain,
% 39.57/5.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 39.57/5.46      | r2_hidden(X1,X0)
% 39.57/5.46      | k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3) != X0
% 39.57/5.46      | sK1 != X1 ),
% 39.57/5.46      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_165,plain,
% 39.57/5.46      ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 39.57/5.46      | r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) ),
% 39.57/5.46      inference(unflattening,[status(thm)],[c_164]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_446,plain,
% 39.57/5.46      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 39.57/5.46      | r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) = iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_17,plain,
% 39.57/5.46      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_19,plain,
% 39.57/5.46      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_166,plain,
% 39.57/5.46      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 39.57/5.46      | r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) = iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_7,plain,
% 39.57/5.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.57/5.46      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.57/5.46      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 39.57/5.46      inference(cnf_transformation,[],[f36]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_477,plain,
% 39.57/5.46      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 39.57/5.46      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 39.57/5.46      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_7]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_478,plain,
% 39.57/5.46      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
% 39.57/5.46      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 39.57/5.46      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 39.57/5.46      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_914,plain,
% 39.57/5.46      ( r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3)) = iProver_top ),
% 39.57/5.46      inference(global_propositional_subsumption,
% 39.57/5.46                [status(thm)],
% 39.57/5.46                [c_446,c_17,c_19,c_166,c_478]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_1551,plain,
% 39.57/5.46      ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
% 39.57/5.46      inference(demodulation,[status(thm)],[c_1378,c_914]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_1554,plain,
% 39.57/5.46      ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,sK3))) ),
% 39.57/5.46      inference(predicate_to_equality_rev,[status(thm)],[c_1551]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_3,plain,
% 39.57/5.46      ( ~ r2_hidden(X0,X1)
% 39.57/5.46      | r2_hidden(X0,X2)
% 39.57/5.46      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 39.57/5.46      inference(cnf_transformation,[],[f48]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_490,plain,
% 39.57/5.46      ( ~ r2_hidden(sK1,X0)
% 39.57/5.46      | r2_hidden(sK1,k4_xboole_0(X0,sK3))
% 39.57/5.46      | r2_hidden(sK1,sK3) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_3]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_608,plain,
% 39.57/5.46      ( ~ r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2))
% 39.57/5.46      | r2_hidden(sK1,k4_xboole_0(k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2),sK3))
% 39.57/5.46      | r2_hidden(sK1,sK3) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_490]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_505,plain,
% 39.57/5.46      ( ~ r2_hidden(sK1,X0)
% 39.57/5.46      | r2_hidden(sK1,k4_xboole_0(X0,sK2))
% 39.57/5.46      | r2_hidden(sK1,sK2) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_3]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_576,plain,
% 39.57/5.46      ( ~ r2_hidden(sK1,k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3))
% 39.57/5.46      | r2_hidden(sK1,k4_xboole_0(k4_subset_1(k1_zfmisc_1(sK1),sK2,sK3),sK2))
% 39.57/5.46      | r2_hidden(sK1,sK2) ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_505]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_222,plain,( X0 = X0 ),theory(equality) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_237,plain,
% 39.57/5.46      ( sK1 = sK1 ),
% 39.57/5.46      inference(instantiation,[status(thm)],[c_222]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_10,plain,
% 39.57/5.46      ( ~ v3_setfam_1(X0,X1)
% 39.57/5.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 39.57/5.46      | ~ r2_hidden(X1,X0) ),
% 39.57/5.46      inference(cnf_transformation,[],[f38]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_15,negated_conjecture,
% 39.57/5.46      ( v3_setfam_1(sK2,sK1) ),
% 39.57/5.46      inference(cnf_transformation,[],[f40]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_185,plain,
% 39.57/5.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 39.57/5.46      | ~ r2_hidden(X1,X0)
% 39.57/5.46      | sK2 != X0
% 39.57/5.46      | sK1 != X1 ),
% 39.57/5.46      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_186,plain,
% 39.57/5.46      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 39.57/5.46      | ~ r2_hidden(sK1,sK2) ),
% 39.57/5.46      inference(unflattening,[status(thm)],[c_185]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_13,negated_conjecture,
% 39.57/5.46      ( v3_setfam_1(sK3,sK1) ),
% 39.57/5.46      inference(cnf_transformation,[],[f42]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_174,plain,
% 39.57/5.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 39.57/5.46      | ~ r2_hidden(X1,X0)
% 39.57/5.46      | sK3 != X0
% 39.57/5.46      | sK1 != X1 ),
% 39.57/5.46      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(c_175,plain,
% 39.57/5.46      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 39.57/5.46      | ~ r2_hidden(sK1,sK3) ),
% 39.57/5.46      inference(unflattening,[status(thm)],[c_174]) ).
% 39.57/5.46  
% 39.57/5.46  cnf(contradiction,plain,
% 39.57/5.46      ( $false ),
% 39.57/5.46      inference(minisat,
% 39.57/5.46                [status(thm)],
% 39.57/5.46                [c_124311,c_54057,c_41450,c_1554,c_608,c_576,c_477,c_237,
% 39.57/5.46                 c_186,c_175,c_165,c_12,c_14]) ).
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  % SZS output end CNFRefutation for theBenchmark.p
% 39.57/5.46  
% 39.57/5.46  ------                               Statistics
% 39.57/5.46  
% 39.57/5.46  ------ General
% 39.57/5.46  
% 39.57/5.46  abstr_ref_over_cycles:                  0
% 39.57/5.46  abstr_ref_under_cycles:                 0
% 39.57/5.46  gc_basic_clause_elim:                   0
% 39.57/5.46  forced_gc_time:                         0
% 39.57/5.46  parsing_time:                           0.012
% 39.57/5.46  unif_index_cands_time:                  0.
% 39.57/5.46  unif_index_add_time:                    0.
% 39.57/5.46  orderings_time:                         0.
% 39.57/5.46  out_proof_time:                         0.012
% 39.57/5.46  total_time:                             4.77
% 39.57/5.46  num_of_symbols:                         43
% 39.57/5.46  num_of_terms:                           217549
% 39.57/5.46  
% 39.57/5.46  ------ Preprocessing
% 39.57/5.46  
% 39.57/5.46  num_of_splits:                          0
% 39.57/5.46  num_of_split_atoms:                     0
% 39.57/5.46  num_of_reused_defs:                     0
% 39.57/5.46  num_eq_ax_congr_red:                    12
% 39.57/5.46  num_of_sem_filtered_clauses:            1
% 39.57/5.46  num_of_subtypes:                        0
% 39.57/5.46  monotx_restored_types:                  0
% 39.57/5.46  sat_num_of_epr_types:                   0
% 39.57/5.46  sat_num_of_non_cyclic_types:            0
% 39.57/5.46  sat_guarded_non_collapsed_types:        0
% 39.57/5.46  num_pure_diseq_elim:                    0
% 39.57/5.46  simp_replaced_by:                       0
% 39.57/5.46  res_preprocessed:                       65
% 39.57/5.46  prep_upred:                             0
% 39.57/5.46  prep_unflattend:                        6
% 39.57/5.46  smt_new_axioms:                         0
% 39.57/5.46  pred_elim_cands:                        3
% 39.57/5.46  pred_elim:                              1
% 39.57/5.46  pred_elim_cl:                           0
% 39.57/5.46  pred_elim_cycles:                       2
% 39.57/5.46  merged_defs:                            0
% 39.57/5.46  merged_defs_ncl:                        0
% 39.57/5.46  bin_hyper_res:                          0
% 39.57/5.46  prep_cycles:                            3
% 39.57/5.46  pred_elim_time:                         0.002
% 39.57/5.46  splitting_time:                         0.
% 39.57/5.46  sem_filter_time:                        0.
% 39.57/5.46  monotx_time:                            0.001
% 39.57/5.46  subtype_inf_time:                       0.
% 39.57/5.46  
% 39.57/5.46  ------ Problem properties
% 39.57/5.46  
% 39.57/5.46  clauses:                                16
% 39.57/5.46  conjectures:                            2
% 39.57/5.46  epr:                                    2
% 39.57/5.46  horn:                                   12
% 39.57/5.46  ground:                                 7
% 39.57/5.46  unary:                                  5
% 39.57/5.46  binary:                                 5
% 39.57/5.46  lits:                                   34
% 39.57/5.46  lits_eq:                                9
% 39.57/5.46  fd_pure:                                0
% 39.57/5.46  fd_pseudo:                              0
% 39.57/5.46  fd_cond:                                0
% 39.57/5.46  fd_pseudo_cond:                         3
% 39.57/5.46  ac_symbols:                             0
% 39.57/5.46  
% 39.57/5.46  ------ Propositional Solver
% 39.57/5.46  
% 39.57/5.46  prop_solver_calls:                      55
% 39.57/5.46  prop_fast_solver_calls:                 1124
% 39.57/5.46  smt_solver_calls:                       0
% 39.57/5.46  smt_fast_solver_calls:                  0
% 39.57/5.46  prop_num_of_clauses:                    54281
% 39.57/5.46  prop_preprocess_simplified:             32807
% 39.57/5.46  prop_fo_subsumed:                       25
% 39.57/5.46  prop_solver_time:                       0.
% 39.57/5.46  smt_solver_time:                        0.
% 39.57/5.46  smt_fast_solver_time:                   0.
% 39.57/5.46  prop_fast_solver_time:                  0.
% 39.57/5.46  prop_unsat_core_time:                   0.004
% 39.57/5.46  
% 39.57/5.46  ------ QBF
% 39.57/5.46  
% 39.57/5.46  qbf_q_res:                              0
% 39.57/5.46  qbf_num_tautologies:                    0
% 39.57/5.46  qbf_prep_cycles:                        0
% 39.57/5.46  
% 39.57/5.46  ------ BMC1
% 39.57/5.46  
% 39.57/5.46  bmc1_current_bound:                     -1
% 39.57/5.46  bmc1_last_solved_bound:                 -1
% 39.57/5.46  bmc1_unsat_core_size:                   -1
% 39.57/5.46  bmc1_unsat_core_parents_size:           -1
% 39.57/5.46  bmc1_merge_next_fun:                    0
% 39.57/5.46  bmc1_unsat_core_clauses_time:           0.
% 39.57/5.46  
% 39.57/5.46  ------ Instantiation
% 39.57/5.46  
% 39.57/5.46  inst_num_of_clauses:                    4659
% 39.57/5.46  inst_num_in_passive:                    1393
% 39.57/5.46  inst_num_in_active:                     1271
% 39.57/5.46  inst_num_in_unprocessed:                1994
% 39.57/5.46  inst_num_of_loops:                      1782
% 39.57/5.46  inst_num_of_learning_restarts:          0
% 39.57/5.46  inst_num_moves_active_passive:          509
% 39.57/5.46  inst_lit_activity:                      0
% 39.57/5.46  inst_lit_activity_moves:                1
% 39.57/5.46  inst_num_tautologies:                   0
% 39.57/5.46  inst_num_prop_implied:                  0
% 39.57/5.46  inst_num_existing_simplified:           0
% 39.57/5.46  inst_num_eq_res_simplified:             0
% 39.57/5.46  inst_num_child_elim:                    0
% 39.57/5.46  inst_num_of_dismatching_blockings:      34900
% 39.57/5.46  inst_num_of_non_proper_insts:           9722
% 39.57/5.46  inst_num_of_duplicates:                 0
% 39.57/5.46  inst_inst_num_from_inst_to_res:         0
% 39.57/5.46  inst_dismatching_checking_time:         0.
% 39.57/5.46  
% 39.57/5.46  ------ Resolution
% 39.57/5.46  
% 39.57/5.46  res_num_of_clauses:                     0
% 39.57/5.46  res_num_in_passive:                     0
% 39.57/5.46  res_num_in_active:                      0
% 39.57/5.46  res_num_of_loops:                       68
% 39.57/5.46  res_forward_subset_subsumed:            1500
% 39.57/5.46  res_backward_subset_subsumed:           0
% 39.57/5.46  res_forward_subsumed:                   0
% 39.57/5.46  res_backward_subsumed:                  0
% 39.57/5.46  res_forward_subsumption_resolution:     0
% 39.57/5.46  res_backward_subsumption_resolution:    0
% 39.57/5.46  res_clause_to_clause_subsumption:       167259
% 39.57/5.46  res_orphan_elimination:                 0
% 39.57/5.46  res_tautology_del:                      228
% 39.57/5.46  res_num_eq_res_simplified:              2
% 39.57/5.46  res_num_sel_changes:                    0
% 39.57/5.46  res_moves_from_active_to_pass:          0
% 39.57/5.46  
% 39.57/5.46  ------ Superposition
% 39.57/5.46  
% 39.57/5.46  sup_time_total:                         0.
% 39.57/5.46  sup_time_generating:                    0.
% 39.57/5.46  sup_time_sim_full:                      0.
% 39.57/5.46  sup_time_sim_immed:                     0.
% 39.57/5.46  
% 39.57/5.46  sup_num_of_clauses:                     10838
% 39.57/5.46  sup_num_in_active:                      352
% 39.57/5.46  sup_num_in_passive:                     10486
% 39.57/5.46  sup_num_of_loops:                       356
% 39.57/5.46  sup_fw_superposition:                   11460
% 39.57/5.46  sup_bw_superposition:                   2646
% 39.57/5.46  sup_immediate_simplified:               3348
% 39.57/5.46  sup_given_eliminated:                   0
% 39.57/5.46  comparisons_done:                       0
% 39.57/5.46  comparisons_avoided:                    0
% 39.57/5.46  
% 39.57/5.46  ------ Simplifications
% 39.57/5.46  
% 39.57/5.46  
% 39.57/5.46  sim_fw_subset_subsumed:                 555
% 39.57/5.46  sim_bw_subset_subsumed:                 0
% 39.57/5.46  sim_fw_subsumed:                        502
% 39.57/5.46  sim_bw_subsumed:                        1
% 39.57/5.46  sim_fw_subsumption_res:                 0
% 39.57/5.46  sim_bw_subsumption_res:                 0
% 39.57/5.46  sim_tautology_del:                      48
% 39.57/5.46  sim_eq_tautology_del:                   84
% 39.57/5.46  sim_eq_res_simp:                        4
% 39.57/5.46  sim_fw_demodulated:                     2804
% 39.57/5.46  sim_bw_demodulated:                     8
% 39.57/5.46  sim_light_normalised:                   346
% 39.57/5.46  sim_joinable_taut:                      0
% 39.57/5.46  sim_joinable_simp:                      0
% 39.57/5.46  sim_ac_normalised:                      0
% 39.57/5.46  sim_smt_subsumption:                    0
% 39.57/5.46  
%------------------------------------------------------------------------------
