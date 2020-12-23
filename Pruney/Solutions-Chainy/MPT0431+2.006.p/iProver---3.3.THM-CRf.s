%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:50 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 225 expanded)
%              Number of clauses        :   59 (  68 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  272 ( 782 expanded)
%              Number of equality atoms :   58 (  77 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_setfam_1(X1,X0)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
           => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      & v3_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X2,X0) )
     => ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,sK2),X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v3_setfam_1(X1,X0) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
          & v3_setfam_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      & v3_setfam_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27])).

fof(f50,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f51,f51,f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_332,plain,
    ( m1_subset_1(k6_subset_1(X0_40,X1_40),k1_zfmisc_1(X0_40)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1445,plain,
    ( m1_subset_1(k6_subset_1(sK2,X0_40),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_11703,plain,
    ( m1_subset_1(k6_subset_1(sK2,sK1),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ r2_hidden(X2_40,X0_40)
    | r2_hidden(X2_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK0,X0_40)
    | r2_hidden(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_8783,plain,
    ( ~ m1_subset_1(k6_subset_1(sK2,sK1),k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK0,k6_subset_1(sK2,sK1))
    | r2_hidden(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_6,plain,
    ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_334,plain,
    ( r1_xboole_0(k6_subset_1(X0_40,X1_40),X1_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_868,plain,
    ( r1_xboole_0(k6_subset_1(X0_40,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_5433,plain,
    ( r1_xboole_0(k6_subset_1(sK2,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_11,plain,
    ( v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,negated_conjecture,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X1,X0)
    | k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_175,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_327,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_175])).

cnf(c_587,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_176,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_175])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
    | m1_subset_1(k4_subset_1(X1_40,X2_40,X0_40),k1_zfmisc_1(X1_40)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_638,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_639,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_855,plain,
    ( r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_19,c_21,c_176,c_639])).

cnf(c_328,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_586,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_329,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_585,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
    | k3_tarski(k2_enumset1(X2_40,X2_40,X2_40,X0_40)) = k4_subset_1(X1_40,X2_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_584,plain,
    ( k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,X1_40)) = k4_subset_1(X2_40,X0_40,X1_40)
    | m1_subset_1(X1_40,k1_zfmisc_1(X2_40)) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(X2_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_1198,plain,
    ( k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,sK2)) = k4_subset_1(k1_zfmisc_1(sK0),X0_40,sK2)
    | m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_584])).

cnf(c_1271,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_586,c_1198])).

cnf(c_5,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k6_subset_1(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_335,plain,
    ( k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,k6_subset_1(X1_40,X0_40))) = k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_336,plain,
    ( r2_hidden(X0_40,X1_40)
    | r2_hidden(X0_40,X2_40)
    | ~ r2_hidden(X0_40,k3_tarski(k2_enumset1(X1_40,X1_40,X1_40,X2_40)))
    | ~ r1_xboole_0(X1_40,X2_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_579,plain,
    ( r2_hidden(X0_40,X1_40) = iProver_top
    | r2_hidden(X0_40,X2_40) = iProver_top
    | r2_hidden(X0_40,k3_tarski(k2_enumset1(X1_40,X1_40,X1_40,X2_40))) != iProver_top
    | r1_xboole_0(X1_40,X2_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_1412,plain,
    ( r2_hidden(X0_40,X1_40) = iProver_top
    | r2_hidden(X0_40,k6_subset_1(X2_40,X1_40)) = iProver_top
    | r2_hidden(X0_40,k3_tarski(k2_enumset1(X1_40,X1_40,X1_40,X2_40))) != iProver_top
    | r1_xboole_0(X1_40,k6_subset_1(X2_40,X1_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_335,c_579])).

cnf(c_1524,plain,
    ( r2_hidden(X0_40,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) != iProver_top
    | r2_hidden(X0_40,k6_subset_1(sK2,sK1)) = iProver_top
    | r2_hidden(X0_40,sK1) = iProver_top
    | r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1271,c_1412])).

cnf(c_4021,plain,
    ( r2_hidden(sK0,k6_subset_1(sK2,sK1)) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top
    | r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_1524])).

cnf(c_4022,plain,
    ( r2_hidden(sK0,k6_subset_1(sK2,sK1))
    | r2_hidden(sK0,sK1)
    | ~ r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4021])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_338,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_688,plain,
    ( ~ r1_xboole_0(X0_40,sK1)
    | r1_xboole_0(sK1,X0_40) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_744,plain,
    ( ~ r1_xboole_0(k6_subset_1(X0_40,sK1),sK1)
    | r1_xboole_0(sK1,k6_subset_1(X0_40,sK1)) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_3798,plain,
    ( ~ r1_xboole_0(k6_subset_1(sK2,sK1),sK1)
    | r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_12,plain,
    ( ~ v3_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_15,negated_conjecture,
    ( v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X0)
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_185,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11703,c_8783,c_5433,c_4022,c_3798,c_196,c_185,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.39/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/1.49  
% 7.39/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.39/1.49  
% 7.39/1.49  ------  iProver source info
% 7.39/1.49  
% 7.39/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.39/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.39/1.49  git: non_committed_changes: false
% 7.39/1.49  git: last_make_outside_of_git: false
% 7.39/1.49  
% 7.39/1.49  ------ 
% 7.39/1.49  
% 7.39/1.49  ------ Input Options
% 7.39/1.49  
% 7.39/1.49  --out_options                           all
% 7.39/1.49  --tptp_safe_out                         true
% 7.39/1.49  --problem_path                          ""
% 7.39/1.49  --include_path                          ""
% 7.39/1.49  --clausifier                            res/vclausify_rel
% 7.39/1.49  --clausifier_options                    ""
% 7.39/1.49  --stdin                                 false
% 7.39/1.49  --stats_out                             all
% 7.39/1.49  
% 7.39/1.49  ------ General Options
% 7.39/1.49  
% 7.39/1.49  --fof                                   false
% 7.39/1.49  --time_out_real                         305.
% 7.39/1.49  --time_out_virtual                      -1.
% 7.39/1.49  --symbol_type_check                     false
% 7.39/1.49  --clausify_out                          false
% 7.39/1.49  --sig_cnt_out                           false
% 7.39/1.49  --trig_cnt_out                          false
% 7.39/1.49  --trig_cnt_out_tolerance                1.
% 7.39/1.49  --trig_cnt_out_sk_spl                   false
% 7.39/1.49  --abstr_cl_out                          false
% 7.39/1.49  
% 7.39/1.49  ------ Global Options
% 7.39/1.49  
% 7.39/1.49  --schedule                              default
% 7.39/1.49  --add_important_lit                     false
% 7.39/1.49  --prop_solver_per_cl                    1000
% 7.39/1.49  --min_unsat_core                        false
% 7.39/1.49  --soft_assumptions                      false
% 7.39/1.49  --soft_lemma_size                       3
% 7.39/1.49  --prop_impl_unit_size                   0
% 7.39/1.49  --prop_impl_unit                        []
% 7.39/1.49  --share_sel_clauses                     true
% 7.39/1.49  --reset_solvers                         false
% 7.39/1.49  --bc_imp_inh                            [conj_cone]
% 7.39/1.49  --conj_cone_tolerance                   3.
% 7.39/1.49  --extra_neg_conj                        none
% 7.39/1.49  --large_theory_mode                     true
% 7.39/1.49  --prolific_symb_bound                   200
% 7.39/1.49  --lt_threshold                          2000
% 7.39/1.49  --clause_weak_htbl                      true
% 7.39/1.49  --gc_record_bc_elim                     false
% 7.39/1.49  
% 7.39/1.49  ------ Preprocessing Options
% 7.39/1.50  
% 7.39/1.50  --preprocessing_flag                    true
% 7.39/1.50  --time_out_prep_mult                    0.1
% 7.39/1.50  --splitting_mode                        input
% 7.39/1.50  --splitting_grd                         true
% 7.39/1.50  --splitting_cvd                         false
% 7.39/1.50  --splitting_cvd_svl                     false
% 7.39/1.50  --splitting_nvd                         32
% 7.39/1.50  --sub_typing                            true
% 7.39/1.50  --prep_gs_sim                           true
% 7.39/1.50  --prep_unflatten                        true
% 7.39/1.50  --prep_res_sim                          true
% 7.39/1.50  --prep_upred                            true
% 7.39/1.50  --prep_sem_filter                       exhaustive
% 7.39/1.50  --prep_sem_filter_out                   false
% 7.39/1.50  --pred_elim                             true
% 7.39/1.50  --res_sim_input                         true
% 7.39/1.50  --eq_ax_congr_red                       true
% 7.39/1.50  --pure_diseq_elim                       true
% 7.39/1.50  --brand_transform                       false
% 7.39/1.50  --non_eq_to_eq                          false
% 7.39/1.50  --prep_def_merge                        true
% 7.39/1.50  --prep_def_merge_prop_impl              false
% 7.39/1.50  --prep_def_merge_mbd                    true
% 7.39/1.50  --prep_def_merge_tr_red                 false
% 7.39/1.50  --prep_def_merge_tr_cl                  false
% 7.39/1.50  --smt_preprocessing                     true
% 7.39/1.50  --smt_ac_axioms                         fast
% 7.39/1.50  --preprocessed_out                      false
% 7.39/1.50  --preprocessed_stats                    false
% 7.39/1.50  
% 7.39/1.50  ------ Abstraction refinement Options
% 7.39/1.50  
% 7.39/1.50  --abstr_ref                             []
% 7.39/1.50  --abstr_ref_prep                        false
% 7.39/1.50  --abstr_ref_until_sat                   false
% 7.39/1.50  --abstr_ref_sig_restrict                funpre
% 7.39/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.50  --abstr_ref_under                       []
% 7.39/1.50  
% 7.39/1.50  ------ SAT Options
% 7.39/1.50  
% 7.39/1.50  --sat_mode                              false
% 7.39/1.50  --sat_fm_restart_options                ""
% 7.39/1.50  --sat_gr_def                            false
% 7.39/1.50  --sat_epr_types                         true
% 7.39/1.50  --sat_non_cyclic_types                  false
% 7.39/1.50  --sat_finite_models                     false
% 7.39/1.50  --sat_fm_lemmas                         false
% 7.39/1.50  --sat_fm_prep                           false
% 7.39/1.50  --sat_fm_uc_incr                        true
% 7.39/1.50  --sat_out_model                         small
% 7.39/1.50  --sat_out_clauses                       false
% 7.39/1.50  
% 7.39/1.50  ------ QBF Options
% 7.39/1.50  
% 7.39/1.50  --qbf_mode                              false
% 7.39/1.50  --qbf_elim_univ                         false
% 7.39/1.50  --qbf_dom_inst                          none
% 7.39/1.50  --qbf_dom_pre_inst                      false
% 7.39/1.50  --qbf_sk_in                             false
% 7.39/1.50  --qbf_pred_elim                         true
% 7.39/1.50  --qbf_split                             512
% 7.39/1.50  
% 7.39/1.50  ------ BMC1 Options
% 7.39/1.50  
% 7.39/1.50  --bmc1_incremental                      false
% 7.39/1.50  --bmc1_axioms                           reachable_all
% 7.39/1.50  --bmc1_min_bound                        0
% 7.39/1.50  --bmc1_max_bound                        -1
% 7.39/1.50  --bmc1_max_bound_default                -1
% 7.39/1.50  --bmc1_symbol_reachability              true
% 7.39/1.50  --bmc1_property_lemmas                  false
% 7.39/1.50  --bmc1_k_induction                      false
% 7.39/1.50  --bmc1_non_equiv_states                 false
% 7.39/1.50  --bmc1_deadlock                         false
% 7.39/1.50  --bmc1_ucm                              false
% 7.39/1.50  --bmc1_add_unsat_core                   none
% 7.39/1.50  --bmc1_unsat_core_children              false
% 7.39/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.50  --bmc1_out_stat                         full
% 7.39/1.50  --bmc1_ground_init                      false
% 7.39/1.50  --bmc1_pre_inst_next_state              false
% 7.39/1.50  --bmc1_pre_inst_state                   false
% 7.39/1.50  --bmc1_pre_inst_reach_state             false
% 7.39/1.50  --bmc1_out_unsat_core                   false
% 7.39/1.50  --bmc1_aig_witness_out                  false
% 7.39/1.50  --bmc1_verbose                          false
% 7.39/1.50  --bmc1_dump_clauses_tptp                false
% 7.39/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.50  --bmc1_dump_file                        -
% 7.39/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.50  --bmc1_ucm_extend_mode                  1
% 7.39/1.50  --bmc1_ucm_init_mode                    2
% 7.39/1.50  --bmc1_ucm_cone_mode                    none
% 7.39/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.50  --bmc1_ucm_relax_model                  4
% 7.39/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.50  --bmc1_ucm_layered_model                none
% 7.39/1.50  --bmc1_ucm_max_lemma_size               10
% 7.39/1.50  
% 7.39/1.50  ------ AIG Options
% 7.39/1.50  
% 7.39/1.50  --aig_mode                              false
% 7.39/1.50  
% 7.39/1.50  ------ Instantiation Options
% 7.39/1.50  
% 7.39/1.50  --instantiation_flag                    true
% 7.39/1.50  --inst_sos_flag                         true
% 7.39/1.50  --inst_sos_phase                        true
% 7.39/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.50  --inst_lit_sel_side                     num_symb
% 7.39/1.50  --inst_solver_per_active                1400
% 7.39/1.50  --inst_solver_calls_frac                1.
% 7.39/1.50  --inst_passive_queue_type               priority_queues
% 7.39/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.50  --inst_passive_queues_freq              [25;2]
% 7.39/1.50  --inst_dismatching                      true
% 7.39/1.50  --inst_eager_unprocessed_to_passive     true
% 7.39/1.50  --inst_prop_sim_given                   true
% 7.39/1.50  --inst_prop_sim_new                     false
% 7.39/1.50  --inst_subs_new                         false
% 7.39/1.50  --inst_eq_res_simp                      false
% 7.39/1.50  --inst_subs_given                       false
% 7.39/1.50  --inst_orphan_elimination               true
% 7.39/1.50  --inst_learning_loop_flag               true
% 7.39/1.50  --inst_learning_start                   3000
% 7.39/1.50  --inst_learning_factor                  2
% 7.39/1.50  --inst_start_prop_sim_after_learn       3
% 7.39/1.50  --inst_sel_renew                        solver
% 7.39/1.50  --inst_lit_activity_flag                true
% 7.39/1.50  --inst_restr_to_given                   false
% 7.39/1.50  --inst_activity_threshold               500
% 7.39/1.50  --inst_out_proof                        true
% 7.39/1.50  
% 7.39/1.50  ------ Resolution Options
% 7.39/1.50  
% 7.39/1.50  --resolution_flag                       true
% 7.39/1.50  --res_lit_sel                           adaptive
% 7.39/1.50  --res_lit_sel_side                      none
% 7.39/1.50  --res_ordering                          kbo
% 7.39/1.50  --res_to_prop_solver                    active
% 7.39/1.50  --res_prop_simpl_new                    false
% 7.39/1.50  --res_prop_simpl_given                  true
% 7.39/1.50  --res_passive_queue_type                priority_queues
% 7.39/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.50  --res_passive_queues_freq               [15;5]
% 7.39/1.50  --res_forward_subs                      full
% 7.39/1.50  --res_backward_subs                     full
% 7.39/1.50  --res_forward_subs_resolution           true
% 7.39/1.50  --res_backward_subs_resolution          true
% 7.39/1.50  --res_orphan_elimination                true
% 7.39/1.50  --res_time_limit                        2.
% 7.39/1.50  --res_out_proof                         true
% 7.39/1.50  
% 7.39/1.50  ------ Superposition Options
% 7.39/1.50  
% 7.39/1.50  --superposition_flag                    true
% 7.39/1.50  --sup_passive_queue_type                priority_queues
% 7.39/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.39/1.50  --demod_completeness_check              fast
% 7.39/1.50  --demod_use_ground                      true
% 7.39/1.50  --sup_to_prop_solver                    passive
% 7.39/1.50  --sup_prop_simpl_new                    true
% 7.39/1.50  --sup_prop_simpl_given                  true
% 7.39/1.50  --sup_fun_splitting                     true
% 7.39/1.50  --sup_smt_interval                      50000
% 7.39/1.50  
% 7.39/1.50  ------ Superposition Simplification Setup
% 7.39/1.50  
% 7.39/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.39/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.39/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.39/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.39/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.39/1.50  --sup_immed_triv                        [TrivRules]
% 7.39/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.50  --sup_immed_bw_main                     []
% 7.39/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.39/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.50  --sup_input_bw                          []
% 7.39/1.50  
% 7.39/1.50  ------ Combination Options
% 7.39/1.50  
% 7.39/1.50  --comb_res_mult                         3
% 7.39/1.50  --comb_sup_mult                         2
% 7.39/1.50  --comb_inst_mult                        10
% 7.39/1.50  
% 7.39/1.50  ------ Debug Options
% 7.39/1.50  
% 7.39/1.50  --dbg_backtrace                         false
% 7.39/1.50  --dbg_dump_prop_clauses                 false
% 7.39/1.50  --dbg_dump_prop_clauses_file            -
% 7.39/1.50  --dbg_out_stat                          false
% 7.39/1.50  ------ Parsing...
% 7.39/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.50  ------ Proving...
% 7.39/1.50  ------ Problem Properties 
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  clauses                                 16
% 7.39/1.50  conjectures                             2
% 7.39/1.50  EPR                                     3
% 7.39/1.50  Horn                                    15
% 7.39/1.50  unary                                   9
% 7.39/1.50  binary                                  2
% 7.39/1.50  lits                                    30
% 7.39/1.50  lits eq                                 4
% 7.39/1.50  fd_pure                                 0
% 7.39/1.50  fd_pseudo                               0
% 7.39/1.50  fd_cond                                 0
% 7.39/1.50  fd_pseudo_cond                          0
% 7.39/1.50  AC symbols                              0
% 7.39/1.50  
% 7.39/1.50  ------ Schedule dynamic 5 is on 
% 7.39/1.50  
% 7.39/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  ------ 
% 7.39/1.50  Current options:
% 7.39/1.50  ------ 
% 7.39/1.50  
% 7.39/1.50  ------ Input Options
% 7.39/1.50  
% 7.39/1.50  --out_options                           all
% 7.39/1.50  --tptp_safe_out                         true
% 7.39/1.50  --problem_path                          ""
% 7.39/1.50  --include_path                          ""
% 7.39/1.50  --clausifier                            res/vclausify_rel
% 7.39/1.50  --clausifier_options                    ""
% 7.39/1.50  --stdin                                 false
% 7.39/1.50  --stats_out                             all
% 7.39/1.50  
% 7.39/1.50  ------ General Options
% 7.39/1.50  
% 7.39/1.50  --fof                                   false
% 7.39/1.50  --time_out_real                         305.
% 7.39/1.50  --time_out_virtual                      -1.
% 7.39/1.50  --symbol_type_check                     false
% 7.39/1.50  --clausify_out                          false
% 7.39/1.50  --sig_cnt_out                           false
% 7.39/1.50  --trig_cnt_out                          false
% 7.39/1.50  --trig_cnt_out_tolerance                1.
% 7.39/1.50  --trig_cnt_out_sk_spl                   false
% 7.39/1.50  --abstr_cl_out                          false
% 7.39/1.50  
% 7.39/1.50  ------ Global Options
% 7.39/1.50  
% 7.39/1.50  --schedule                              default
% 7.39/1.50  --add_important_lit                     false
% 7.39/1.50  --prop_solver_per_cl                    1000
% 7.39/1.50  --min_unsat_core                        false
% 7.39/1.50  --soft_assumptions                      false
% 7.39/1.50  --soft_lemma_size                       3
% 7.39/1.50  --prop_impl_unit_size                   0
% 7.39/1.50  --prop_impl_unit                        []
% 7.39/1.50  --share_sel_clauses                     true
% 7.39/1.50  --reset_solvers                         false
% 7.39/1.50  --bc_imp_inh                            [conj_cone]
% 7.39/1.50  --conj_cone_tolerance                   3.
% 7.39/1.50  --extra_neg_conj                        none
% 7.39/1.50  --large_theory_mode                     true
% 7.39/1.50  --prolific_symb_bound                   200
% 7.39/1.50  --lt_threshold                          2000
% 7.39/1.50  --clause_weak_htbl                      true
% 7.39/1.50  --gc_record_bc_elim                     false
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing Options
% 7.39/1.50  
% 7.39/1.50  --preprocessing_flag                    true
% 7.39/1.50  --time_out_prep_mult                    0.1
% 7.39/1.50  --splitting_mode                        input
% 7.39/1.50  --splitting_grd                         true
% 7.39/1.50  --splitting_cvd                         false
% 7.39/1.50  --splitting_cvd_svl                     false
% 7.39/1.50  --splitting_nvd                         32
% 7.39/1.50  --sub_typing                            true
% 7.39/1.50  --prep_gs_sim                           true
% 7.39/1.50  --prep_unflatten                        true
% 7.39/1.50  --prep_res_sim                          true
% 7.39/1.50  --prep_upred                            true
% 7.39/1.50  --prep_sem_filter                       exhaustive
% 7.39/1.50  --prep_sem_filter_out                   false
% 7.39/1.50  --pred_elim                             true
% 7.39/1.50  --res_sim_input                         true
% 7.39/1.50  --eq_ax_congr_red                       true
% 7.39/1.50  --pure_diseq_elim                       true
% 7.39/1.50  --brand_transform                       false
% 7.39/1.50  --non_eq_to_eq                          false
% 7.39/1.50  --prep_def_merge                        true
% 7.39/1.50  --prep_def_merge_prop_impl              false
% 7.39/1.50  --prep_def_merge_mbd                    true
% 7.39/1.50  --prep_def_merge_tr_red                 false
% 7.39/1.50  --prep_def_merge_tr_cl                  false
% 7.39/1.50  --smt_preprocessing                     true
% 7.39/1.50  --smt_ac_axioms                         fast
% 7.39/1.50  --preprocessed_out                      false
% 7.39/1.50  --preprocessed_stats                    false
% 7.39/1.50  
% 7.39/1.50  ------ Abstraction refinement Options
% 7.39/1.50  
% 7.39/1.50  --abstr_ref                             []
% 7.39/1.50  --abstr_ref_prep                        false
% 7.39/1.50  --abstr_ref_until_sat                   false
% 7.39/1.50  --abstr_ref_sig_restrict                funpre
% 7.39/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.50  --abstr_ref_under                       []
% 7.39/1.50  
% 7.39/1.50  ------ SAT Options
% 7.39/1.50  
% 7.39/1.50  --sat_mode                              false
% 7.39/1.50  --sat_fm_restart_options                ""
% 7.39/1.50  --sat_gr_def                            false
% 7.39/1.50  --sat_epr_types                         true
% 7.39/1.50  --sat_non_cyclic_types                  false
% 7.39/1.50  --sat_finite_models                     false
% 7.39/1.50  --sat_fm_lemmas                         false
% 7.39/1.50  --sat_fm_prep                           false
% 7.39/1.50  --sat_fm_uc_incr                        true
% 7.39/1.50  --sat_out_model                         small
% 7.39/1.50  --sat_out_clauses                       false
% 7.39/1.50  
% 7.39/1.50  ------ QBF Options
% 7.39/1.50  
% 7.39/1.50  --qbf_mode                              false
% 7.39/1.50  --qbf_elim_univ                         false
% 7.39/1.50  --qbf_dom_inst                          none
% 7.39/1.50  --qbf_dom_pre_inst                      false
% 7.39/1.50  --qbf_sk_in                             false
% 7.39/1.50  --qbf_pred_elim                         true
% 7.39/1.50  --qbf_split                             512
% 7.39/1.50  
% 7.39/1.50  ------ BMC1 Options
% 7.39/1.50  
% 7.39/1.50  --bmc1_incremental                      false
% 7.39/1.50  --bmc1_axioms                           reachable_all
% 7.39/1.50  --bmc1_min_bound                        0
% 7.39/1.50  --bmc1_max_bound                        -1
% 7.39/1.50  --bmc1_max_bound_default                -1
% 7.39/1.50  --bmc1_symbol_reachability              true
% 7.39/1.50  --bmc1_property_lemmas                  false
% 7.39/1.50  --bmc1_k_induction                      false
% 7.39/1.50  --bmc1_non_equiv_states                 false
% 7.39/1.50  --bmc1_deadlock                         false
% 7.39/1.50  --bmc1_ucm                              false
% 7.39/1.50  --bmc1_add_unsat_core                   none
% 7.39/1.50  --bmc1_unsat_core_children              false
% 7.39/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.50  --bmc1_out_stat                         full
% 7.39/1.50  --bmc1_ground_init                      false
% 7.39/1.50  --bmc1_pre_inst_next_state              false
% 7.39/1.50  --bmc1_pre_inst_state                   false
% 7.39/1.50  --bmc1_pre_inst_reach_state             false
% 7.39/1.50  --bmc1_out_unsat_core                   false
% 7.39/1.50  --bmc1_aig_witness_out                  false
% 7.39/1.50  --bmc1_verbose                          false
% 7.39/1.50  --bmc1_dump_clauses_tptp                false
% 7.39/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.50  --bmc1_dump_file                        -
% 7.39/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.50  --bmc1_ucm_extend_mode                  1
% 7.39/1.50  --bmc1_ucm_init_mode                    2
% 7.39/1.50  --bmc1_ucm_cone_mode                    none
% 7.39/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.50  --bmc1_ucm_relax_model                  4
% 7.39/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.50  --bmc1_ucm_layered_model                none
% 7.39/1.50  --bmc1_ucm_max_lemma_size               10
% 7.39/1.50  
% 7.39/1.50  ------ AIG Options
% 7.39/1.50  
% 7.39/1.50  --aig_mode                              false
% 7.39/1.50  
% 7.39/1.50  ------ Instantiation Options
% 7.39/1.50  
% 7.39/1.50  --instantiation_flag                    true
% 7.39/1.50  --inst_sos_flag                         true
% 7.39/1.50  --inst_sos_phase                        true
% 7.39/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.50  --inst_lit_sel_side                     none
% 7.39/1.50  --inst_solver_per_active                1400
% 7.39/1.50  --inst_solver_calls_frac                1.
% 7.39/1.50  --inst_passive_queue_type               priority_queues
% 7.39/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.50  --inst_passive_queues_freq              [25;2]
% 7.39/1.50  --inst_dismatching                      true
% 7.39/1.50  --inst_eager_unprocessed_to_passive     true
% 7.39/1.50  --inst_prop_sim_given                   true
% 7.39/1.50  --inst_prop_sim_new                     false
% 7.39/1.50  --inst_subs_new                         false
% 7.39/1.50  --inst_eq_res_simp                      false
% 7.39/1.50  --inst_subs_given                       false
% 7.39/1.50  --inst_orphan_elimination               true
% 7.39/1.50  --inst_learning_loop_flag               true
% 7.39/1.50  --inst_learning_start                   3000
% 7.39/1.50  --inst_learning_factor                  2
% 7.39/1.50  --inst_start_prop_sim_after_learn       3
% 7.39/1.50  --inst_sel_renew                        solver
% 7.39/1.50  --inst_lit_activity_flag                true
% 7.39/1.50  --inst_restr_to_given                   false
% 7.39/1.50  --inst_activity_threshold               500
% 7.39/1.50  --inst_out_proof                        true
% 7.39/1.50  
% 7.39/1.50  ------ Resolution Options
% 7.39/1.50  
% 7.39/1.50  --resolution_flag                       false
% 7.39/1.50  --res_lit_sel                           adaptive
% 7.39/1.50  --res_lit_sel_side                      none
% 7.39/1.50  --res_ordering                          kbo
% 7.39/1.50  --res_to_prop_solver                    active
% 7.39/1.50  --res_prop_simpl_new                    false
% 7.39/1.50  --res_prop_simpl_given                  true
% 7.39/1.50  --res_passive_queue_type                priority_queues
% 7.39/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.50  --res_passive_queues_freq               [15;5]
% 7.39/1.50  --res_forward_subs                      full
% 7.39/1.50  --res_backward_subs                     full
% 7.39/1.50  --res_forward_subs_resolution           true
% 7.39/1.50  --res_backward_subs_resolution          true
% 7.39/1.50  --res_orphan_elimination                true
% 7.39/1.50  --res_time_limit                        2.
% 7.39/1.50  --res_out_proof                         true
% 7.39/1.50  
% 7.39/1.50  ------ Superposition Options
% 7.39/1.50  
% 7.39/1.50  --superposition_flag                    true
% 7.39/1.50  --sup_passive_queue_type                priority_queues
% 7.39/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.39/1.50  --demod_completeness_check              fast
% 7.39/1.50  --demod_use_ground                      true
% 7.39/1.50  --sup_to_prop_solver                    passive
% 7.39/1.50  --sup_prop_simpl_new                    true
% 7.39/1.50  --sup_prop_simpl_given                  true
% 7.39/1.50  --sup_fun_splitting                     true
% 7.39/1.50  --sup_smt_interval                      50000
% 7.39/1.50  
% 7.39/1.50  ------ Superposition Simplification Setup
% 7.39/1.50  
% 7.39/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.39/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.39/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.39/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.39/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.39/1.50  --sup_immed_triv                        [TrivRules]
% 7.39/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.50  --sup_immed_bw_main                     []
% 7.39/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.39/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.50  --sup_input_bw                          []
% 7.39/1.50  
% 7.39/1.50  ------ Combination Options
% 7.39/1.50  
% 7.39/1.50  --comb_res_mult                         3
% 7.39/1.50  --comb_sup_mult                         2
% 7.39/1.50  --comb_inst_mult                        10
% 7.39/1.50  
% 7.39/1.50  ------ Debug Options
% 7.39/1.50  
% 7.39/1.50  --dbg_backtrace                         false
% 7.39/1.50  --dbg_dump_prop_clauses                 false
% 7.39/1.50  --dbg_dump_prop_clauses_file            -
% 7.39/1.50  --dbg_out_stat                          false
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  ------ Proving...
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  % SZS status Theorem for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  fof(f8,axiom,(
% 7.39/1.50    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f40,plain,(
% 7.39/1.50    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f8])).
% 7.39/1.50  
% 7.39/1.50  fof(f9,axiom,(
% 7.39/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f20,plain,(
% 7.39/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.50    inference(ennf_transformation,[],[f9])).
% 7.39/1.50  
% 7.39/1.50  fof(f41,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f20])).
% 7.39/1.50  
% 7.39/1.50  fof(f4,axiom,(
% 7.39/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f36,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f4])).
% 7.39/1.50  
% 7.39/1.50  fof(f11,axiom,(
% 7.39/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f43,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f11])).
% 7.39/1.50  
% 7.39/1.50  fof(f57,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f36,f43])).
% 7.39/1.50  
% 7.39/1.50  fof(f12,axiom,(
% 7.39/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f23,plain,(
% 7.39/1.50    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.39/1.50    inference(ennf_transformation,[],[f12])).
% 7.39/1.50  
% 7.39/1.50  fof(f26,plain,(
% 7.39/1.50    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.39/1.50    inference(nnf_transformation,[],[f23])).
% 7.39/1.50  
% 7.39/1.50  fof(f45,plain,(
% 7.39/1.50    ( ! [X0,X1] : (v3_setfam_1(X1,X0) | r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f26])).
% 7.39/1.50  
% 7.39/1.50  fof(f13,conjecture,(
% 7.39/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f14,negated_conjecture,(
% 7.39/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 7.39/1.50    inference(negated_conjecture,[],[f13])).
% 7.39/1.50  
% 7.39/1.50  fof(f15,plain,(
% 7.39/1.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)))),
% 7.39/1.50    inference(pure_predicate_removal,[],[f14])).
% 7.39/1.50  
% 7.39/1.50  fof(f24,plain,(
% 7.39/1.50    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)))),
% 7.39/1.50    inference(ennf_transformation,[],[f15])).
% 7.39/1.50  
% 7.39/1.50  fof(f25,plain,(
% 7.39/1.50    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))),
% 7.39/1.50    inference(flattening,[],[f24])).
% 7.39/1.50  
% 7.39/1.50  fof(f28,plain,(
% 7.39/1.50    ( ! [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,sK2),X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(sK2,X0))) )),
% 7.39/1.50    introduced(choice_axiom,[])).
% 7.39/1.50  
% 7.39/1.50  fof(f27,plain,(
% 7.39/1.50    ? [X0,X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK1,sK0))),
% 7.39/1.50    introduced(choice_axiom,[])).
% 7.39/1.50  
% 7.39/1.50  fof(f29,plain,(
% 7.39/1.50    (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK1,sK0)),
% 7.39/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27])).
% 7.39/1.50  
% 7.39/1.50  fof(f50,plain,(
% 7.39/1.50    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 7.39/1.50    inference(cnf_transformation,[],[f29])).
% 7.39/1.50  
% 7.39/1.50  fof(f47,plain,(
% 7.39/1.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 7.39/1.50    inference(cnf_transformation,[],[f29])).
% 7.39/1.50  
% 7.39/1.50  fof(f49,plain,(
% 7.39/1.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 7.39/1.50    inference(cnf_transformation,[],[f29])).
% 7.39/1.50  
% 7.39/1.50  fof(f7,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f18,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.39/1.50    inference(ennf_transformation,[],[f7])).
% 7.39/1.50  
% 7.39/1.50  fof(f19,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.50    inference(flattening,[],[f18])).
% 7.39/1.50  
% 7.39/1.50  fof(f39,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f19])).
% 7.39/1.50  
% 7.39/1.50  fof(f10,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f21,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.39/1.50    inference(ennf_transformation,[],[f10])).
% 7.39/1.50  
% 7.39/1.50  fof(f22,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.39/1.50    inference(flattening,[],[f21])).
% 7.39/1.50  
% 7.39/1.50  fof(f42,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f22])).
% 7.39/1.50  
% 7.39/1.50  fof(f6,axiom,(
% 7.39/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f38,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f6])).
% 7.39/1.50  
% 7.39/1.50  fof(f5,axiom,(
% 7.39/1.50    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f37,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f5])).
% 7.39/1.50  
% 7.39/1.50  fof(f51,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 7.39/1.50    inference(definition_unfolding,[],[f38,f37])).
% 7.39/1.50  
% 7.39/1.50  fof(f58,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.39/1.50    inference(definition_unfolding,[],[f42,f51])).
% 7.39/1.50  
% 7.39/1.50  fof(f3,axiom,(
% 7.39/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f35,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f3])).
% 7.39/1.50  
% 7.39/1.50  fof(f56,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k6_subset_1(X1,X0)))) )),
% 7.39/1.50    inference(definition_unfolding,[],[f35,f51,f51,f43])).
% 7.39/1.50  
% 7.39/1.50  fof(f2,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f17,plain,(
% 7.39/1.50    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 7.39/1.50    inference(ennf_transformation,[],[f2])).
% 7.39/1.50  
% 7.39/1.50  fof(f31,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f17])).
% 7.39/1.50  
% 7.39/1.50  fof(f55,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f31,f51])).
% 7.39/1.50  
% 7.39/1.50  fof(f1,axiom,(
% 7.39/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f16,plain,(
% 7.39/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.39/1.50    inference(ennf_transformation,[],[f1])).
% 7.39/1.50  
% 7.39/1.50  fof(f30,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f16])).
% 7.39/1.50  
% 7.39/1.50  fof(f44,plain,(
% 7.39/1.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f26])).
% 7.39/1.50  
% 7.39/1.50  fof(f46,plain,(
% 7.39/1.50    v3_setfam_1(sK1,sK0)),
% 7.39/1.50    inference(cnf_transformation,[],[f29])).
% 7.39/1.50  
% 7.39/1.50  fof(f48,plain,(
% 7.39/1.50    v3_setfam_1(sK2,sK0)),
% 7.39/1.50    inference(cnf_transformation,[],[f29])).
% 7.39/1.50  
% 7.39/1.50  cnf(c_8,plain,
% 7.39/1.50      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 7.39/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_332,plain,
% 7.39/1.50      ( m1_subset_1(k6_subset_1(X0_40,X1_40),k1_zfmisc_1(X0_40)) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1445,plain,
% 7.39/1.50      ( m1_subset_1(k6_subset_1(sK2,X0_40),k1_zfmisc_1(sK2)) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_332]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_11703,plain,
% 7.39/1.50      ( m1_subset_1(k6_subset_1(sK2,sK1),k1_zfmisc_1(sK2)) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_1445]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_9,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.39/1.50      | ~ r2_hidden(X2,X0)
% 7.39/1.50      | r2_hidden(X2,X1) ),
% 7.39/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_331,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.39/1.50      | ~ r2_hidden(X2_40,X0_40)
% 7.39/1.50      | r2_hidden(X2_40,X1_40) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_623,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(sK2))
% 7.39/1.50      | ~ r2_hidden(sK0,X0_40)
% 7.39/1.50      | r2_hidden(sK0,sK2) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_331]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_8783,plain,
% 7.39/1.50      ( ~ m1_subset_1(k6_subset_1(sK2,sK1),k1_zfmisc_1(sK2))
% 7.39/1.50      | ~ r2_hidden(sK0,k6_subset_1(sK2,sK1))
% 7.39/1.50      | r2_hidden(sK0,sK2) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_623]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_6,plain,
% 7.39/1.50      ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
% 7.39/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_334,plain,
% 7.39/1.50      ( r1_xboole_0(k6_subset_1(X0_40,X1_40),X1_40) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_868,plain,
% 7.39/1.50      ( r1_xboole_0(k6_subset_1(X0_40,sK1),sK1) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_334]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5433,plain,
% 7.39/1.50      ( r1_xboole_0(k6_subset_1(sK2,sK1),sK1) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_868]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_11,plain,
% 7.39/1.50      ( v3_setfam_1(X0,X1)
% 7.39/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.39/1.50      | r2_hidden(X1,X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_13,negated_conjecture,
% 7.39/1.50      ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_174,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.39/1.50      | r2_hidden(X1,X0)
% 7.39/1.50      | k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) != X0
% 7.39/1.50      | sK0 != X1 ),
% 7.39/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_175,plain,
% 7.39/1.50      ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 7.39/1.50      | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) ),
% 7.39/1.50      inference(unflattening,[status(thm)],[c_174]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_327,plain,
% 7.39/1.50      ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 7.39/1.50      | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_175]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_587,plain,
% 7.39/1.50      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 7.39/1.50      | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_16,negated_conjecture,
% 7.39/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 7.39/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_19,plain,
% 7.39/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_14,negated_conjecture,
% 7.39/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 7.39/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_21,plain,
% 7.39/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_176,plain,
% 7.39/1.50      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 7.39/1.50      | r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_175]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_7,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.39/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.39/1.50      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.39/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_333,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.39/1.50      | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
% 7.39/1.50      | m1_subset_1(k4_subset_1(X1_40,X2_40,X0_40),k1_zfmisc_1(X1_40)) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_638,plain,
% 7.39/1.50      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 7.39/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 7.39/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_333]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_639,plain,
% 7.39/1.50      ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
% 7.39/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 7.39/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_855,plain,
% 7.39/1.50      ( r2_hidden(sK0,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) = iProver_top ),
% 7.39/1.50      inference(global_propositional_subsumption,
% 7.39/1.50                [status(thm)],
% 7.39/1.50                [c_587,c_19,c_21,c_176,c_639]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_328,negated_conjecture,
% 7.39/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_586,plain,
% 7.39/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_329,negated_conjecture,
% 7.39/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_585,plain,
% 7.39/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_10,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.39/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.39/1.50      | k3_tarski(k2_enumset1(X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_330,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.39/1.50      | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
% 7.39/1.50      | k3_tarski(k2_enumset1(X2_40,X2_40,X2_40,X0_40)) = k4_subset_1(X1_40,X2_40,X0_40) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_584,plain,
% 7.39/1.50      ( k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,X1_40)) = k4_subset_1(X2_40,X0_40,X1_40)
% 7.39/1.50      | m1_subset_1(X1_40,k1_zfmisc_1(X2_40)) != iProver_top
% 7.39/1.50      | m1_subset_1(X0_40,k1_zfmisc_1(X2_40)) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1198,plain,
% 7.39/1.50      ( k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,sK2)) = k4_subset_1(k1_zfmisc_1(sK0),X0_40,sK2)
% 7.39/1.50      | m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_585,c_584]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1271,plain,
% 7.39/1.50      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_586,c_1198]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5,plain,
% 7.39/1.50      ( k3_tarski(k2_enumset1(X0,X0,X0,k6_subset_1(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 7.39/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_335,plain,
% 7.39/1.50      ( k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,k6_subset_1(X1_40,X0_40))) = k3_tarski(k2_enumset1(X0_40,X0_40,X0_40,X1_40)) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4,plain,
% 7.39/1.50      ( r2_hidden(X0,X1)
% 7.39/1.50      | r2_hidden(X0,X2)
% 7.39/1.50      | ~ r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
% 7.39/1.50      | ~ r1_xboole_0(X1,X2) ),
% 7.39/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_336,plain,
% 7.39/1.50      ( r2_hidden(X0_40,X1_40)
% 7.39/1.50      | r2_hidden(X0_40,X2_40)
% 7.39/1.50      | ~ r2_hidden(X0_40,k3_tarski(k2_enumset1(X1_40,X1_40,X1_40,X2_40)))
% 7.39/1.50      | ~ r1_xboole_0(X1_40,X2_40) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_579,plain,
% 7.39/1.50      ( r2_hidden(X0_40,X1_40) = iProver_top
% 7.39/1.50      | r2_hidden(X0_40,X2_40) = iProver_top
% 7.39/1.50      | r2_hidden(X0_40,k3_tarski(k2_enumset1(X1_40,X1_40,X1_40,X2_40))) != iProver_top
% 7.39/1.50      | r1_xboole_0(X1_40,X2_40) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1412,plain,
% 7.39/1.50      ( r2_hidden(X0_40,X1_40) = iProver_top
% 7.39/1.50      | r2_hidden(X0_40,k6_subset_1(X2_40,X1_40)) = iProver_top
% 7.39/1.50      | r2_hidden(X0_40,k3_tarski(k2_enumset1(X1_40,X1_40,X1_40,X2_40))) != iProver_top
% 7.39/1.50      | r1_xboole_0(X1_40,k6_subset_1(X2_40,X1_40)) != iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_335,c_579]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1524,plain,
% 7.39/1.50      ( r2_hidden(X0_40,k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2)) != iProver_top
% 7.39/1.50      | r2_hidden(X0_40,k6_subset_1(sK2,sK1)) = iProver_top
% 7.39/1.50      | r2_hidden(X0_40,sK1) = iProver_top
% 7.39/1.50      | r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) != iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_1271,c_1412]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4021,plain,
% 7.39/1.50      ( r2_hidden(sK0,k6_subset_1(sK2,sK1)) = iProver_top
% 7.39/1.50      | r2_hidden(sK0,sK1) = iProver_top
% 7.39/1.50      | r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) != iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_855,c_1524]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4022,plain,
% 7.39/1.50      ( r2_hidden(sK0,k6_subset_1(sK2,sK1))
% 7.39/1.50      | r2_hidden(sK0,sK1)
% 7.39/1.50      | ~ r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) ),
% 7.39/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4021]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_0,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_338,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_40,X1_40) | r1_xboole_0(X1_40,X0_40) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_688,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_40,sK1) | r1_xboole_0(sK1,X0_40) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_338]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_744,plain,
% 7.39/1.50      ( ~ r1_xboole_0(k6_subset_1(X0_40,sK1),sK1)
% 7.39/1.50      | r1_xboole_0(sK1,k6_subset_1(X0_40,sK1)) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_688]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_3798,plain,
% 7.39/1.50      ( ~ r1_xboole_0(k6_subset_1(sK2,sK1),sK1)
% 7.39/1.50      | r1_xboole_0(sK1,k6_subset_1(sK2,sK1)) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_744]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_12,plain,
% 7.39/1.50      ( ~ v3_setfam_1(X0,X1)
% 7.39/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.39/1.50      | ~ r2_hidden(X1,X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_17,negated_conjecture,
% 7.39/1.50      ( v3_setfam_1(sK1,sK0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_195,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.39/1.50      | ~ r2_hidden(X1,X0)
% 7.39/1.50      | sK1 != X0
% 7.39/1.50      | sK0 != X1 ),
% 7.39/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_196,plain,
% 7.39/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 7.39/1.50      | ~ r2_hidden(sK0,sK1) ),
% 7.39/1.50      inference(unflattening,[status(thm)],[c_195]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_15,negated_conjecture,
% 7.39/1.50      ( v3_setfam_1(sK2,sK0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_184,plain,
% 7.39/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.39/1.50      | ~ r2_hidden(X1,X0)
% 7.39/1.50      | sK2 != X0
% 7.39/1.50      | sK0 != X1 ),
% 7.39/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_185,plain,
% 7.39/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 7.39/1.50      | ~ r2_hidden(sK0,sK2) ),
% 7.39/1.50      inference(unflattening,[status(thm)],[c_184]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(contradiction,plain,
% 7.39/1.50      ( $false ),
% 7.39/1.50      inference(minisat,
% 7.39/1.50                [status(thm)],
% 7.39/1.50                [c_11703,c_8783,c_5433,c_4022,c_3798,c_196,c_185,c_14,
% 7.39/1.50                 c_16]) ).
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  ------                               Statistics
% 7.39/1.50  
% 7.39/1.50  ------ General
% 7.39/1.50  
% 7.39/1.50  abstr_ref_over_cycles:                  0
% 7.39/1.50  abstr_ref_under_cycles:                 0
% 7.39/1.50  gc_basic_clause_elim:                   0
% 7.39/1.50  forced_gc_time:                         0
% 7.39/1.50  parsing_time:                           0.008
% 7.39/1.50  unif_index_cands_time:                  0.
% 7.39/1.50  unif_index_add_time:                    0.
% 7.39/1.50  orderings_time:                         0.
% 7.39/1.50  out_proof_time:                         0.007
% 7.39/1.50  total_time:                             0.539
% 7.39/1.50  num_of_symbols:                         45
% 7.39/1.50  num_of_terms:                           13321
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing
% 7.39/1.50  
% 7.39/1.50  num_of_splits:                          0
% 7.39/1.50  num_of_split_atoms:                     0
% 7.39/1.50  num_of_reused_defs:                     0
% 7.39/1.50  num_eq_ax_congr_red:                    19
% 7.39/1.50  num_of_sem_filtered_clauses:            1
% 7.39/1.50  num_of_subtypes:                        2
% 7.39/1.50  monotx_restored_types:                  0
% 7.39/1.50  sat_num_of_epr_types:                   0
% 7.39/1.50  sat_num_of_non_cyclic_types:            0
% 7.39/1.50  sat_guarded_non_collapsed_types:        0
% 7.39/1.50  num_pure_diseq_elim:                    0
% 7.39/1.50  simp_replaced_by:                       0
% 7.39/1.50  res_preprocessed:                       85
% 7.39/1.50  prep_upred:                             0
% 7.39/1.50  prep_unflattend:                        6
% 7.39/1.50  smt_new_axioms:                         0
% 7.39/1.50  pred_elim_cands:                        3
% 7.39/1.50  pred_elim:                              1
% 7.39/1.50  pred_elim_cl:                           0
% 7.39/1.50  pred_elim_cycles:                       3
% 7.39/1.50  merged_defs:                            0
% 7.39/1.50  merged_defs_ncl:                        0
% 7.39/1.50  bin_hyper_res:                          0
% 7.39/1.50  prep_cycles:                            4
% 7.39/1.50  pred_elim_time:                         0.002
% 7.39/1.50  splitting_time:                         0.
% 7.39/1.50  sem_filter_time:                        0.
% 7.39/1.50  monotx_time:                            0.
% 7.39/1.50  subtype_inf_time:                       0.
% 7.39/1.50  
% 7.39/1.50  ------ Problem properties
% 7.39/1.50  
% 7.39/1.50  clauses:                                16
% 7.39/1.50  conjectures:                            2
% 7.39/1.50  epr:                                    3
% 7.39/1.50  horn:                                   15
% 7.39/1.50  ground:                                 7
% 7.39/1.50  unary:                                  9
% 7.39/1.50  binary:                                 2
% 7.39/1.50  lits:                                   30
% 7.39/1.50  lits_eq:                                4
% 7.39/1.50  fd_pure:                                0
% 7.39/1.50  fd_pseudo:                              0
% 7.39/1.50  fd_cond:                                0
% 7.39/1.50  fd_pseudo_cond:                         0
% 7.39/1.50  ac_symbols:                             0
% 7.39/1.50  
% 7.39/1.50  ------ Propositional Solver
% 7.39/1.50  
% 7.39/1.50  prop_solver_calls:                      35
% 7.39/1.50  prop_fast_solver_calls:                 818
% 7.39/1.50  smt_solver_calls:                       0
% 7.39/1.50  smt_fast_solver_calls:                  0
% 7.39/1.50  prop_num_of_clauses:                    5008
% 7.39/1.50  prop_preprocess_simplified:             9992
% 7.39/1.50  prop_fo_subsumed:                       20
% 7.39/1.50  prop_solver_time:                       0.
% 7.39/1.50  smt_solver_time:                        0.
% 7.39/1.50  smt_fast_solver_time:                   0.
% 7.39/1.50  prop_fast_solver_time:                  0.
% 7.39/1.50  prop_unsat_core_time:                   0.
% 7.39/1.50  
% 7.39/1.50  ------ QBF
% 7.39/1.50  
% 7.39/1.50  qbf_q_res:                              0
% 7.39/1.50  qbf_num_tautologies:                    0
% 7.39/1.50  qbf_prep_cycles:                        0
% 7.39/1.50  
% 7.39/1.50  ------ BMC1
% 7.39/1.50  
% 7.39/1.50  bmc1_current_bound:                     -1
% 7.39/1.50  bmc1_last_solved_bound:                 -1
% 7.39/1.50  bmc1_unsat_core_size:                   -1
% 7.39/1.50  bmc1_unsat_core_parents_size:           -1
% 7.39/1.50  bmc1_merge_next_fun:                    0
% 7.39/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.39/1.50  
% 7.39/1.50  ------ Instantiation
% 7.39/1.50  
% 7.39/1.50  inst_num_of_clauses:                    1283
% 7.39/1.50  inst_num_in_passive:                    349
% 7.39/1.50  inst_num_in_active:                     824
% 7.39/1.50  inst_num_in_unprocessed:                109
% 7.39/1.50  inst_num_of_loops:                      870
% 7.39/1.50  inst_num_of_learning_restarts:          0
% 7.39/1.50  inst_num_moves_active_passive:          39
% 7.39/1.50  inst_lit_activity:                      0
% 7.39/1.50  inst_lit_activity_moves:                0
% 7.39/1.50  inst_num_tautologies:                   0
% 7.39/1.50  inst_num_prop_implied:                  0
% 7.39/1.50  inst_num_existing_simplified:           0
% 7.39/1.50  inst_num_eq_res_simplified:             0
% 7.39/1.50  inst_num_child_elim:                    0
% 7.39/1.50  inst_num_of_dismatching_blockings:      689
% 7.39/1.50  inst_num_of_non_proper_insts:           2387
% 7.39/1.50  inst_num_of_duplicates:                 0
% 7.39/1.50  inst_inst_num_from_inst_to_res:         0
% 7.39/1.50  inst_dismatching_checking_time:         0.
% 7.39/1.50  
% 7.39/1.50  ------ Resolution
% 7.39/1.50  
% 7.39/1.50  res_num_of_clauses:                     0
% 7.39/1.50  res_num_in_passive:                     0
% 7.39/1.50  res_num_in_active:                      0
% 7.39/1.50  res_num_of_loops:                       89
% 7.39/1.50  res_forward_subset_subsumed:            172
% 7.39/1.50  res_backward_subset_subsumed:           4
% 7.39/1.50  res_forward_subsumed:                   0
% 7.39/1.50  res_backward_subsumed:                  0
% 7.39/1.50  res_forward_subsumption_resolution:     0
% 7.39/1.50  res_backward_subsumption_resolution:    0
% 7.39/1.50  res_clause_to_clause_subsumption:       1312
% 7.39/1.50  res_orphan_elimination:                 0
% 7.39/1.50  res_tautology_del:                      276
% 7.39/1.50  res_num_eq_res_simplified:              2
% 7.39/1.50  res_num_sel_changes:                    0
% 7.39/1.50  res_moves_from_active_to_pass:          0
% 7.39/1.50  
% 7.39/1.50  ------ Superposition
% 7.39/1.50  
% 7.39/1.50  sup_time_total:                         0.
% 7.39/1.50  sup_time_generating:                    0.
% 7.39/1.50  sup_time_sim_full:                      0.
% 7.39/1.50  sup_time_sim_immed:                     0.
% 7.39/1.50  
% 7.39/1.50  sup_num_of_clauses:                     485
% 7.39/1.50  sup_num_in_active:                      158
% 7.39/1.50  sup_num_in_passive:                     327
% 7.39/1.50  sup_num_of_loops:                       172
% 7.39/1.50  sup_fw_superposition:                   173
% 7.39/1.50  sup_bw_superposition:                   343
% 7.39/1.50  sup_immediate_simplified:               29
% 7.39/1.50  sup_given_eliminated:                   0
% 7.39/1.50  comparisons_done:                       0
% 7.39/1.50  comparisons_avoided:                    0
% 7.39/1.50  
% 7.39/1.50  ------ Simplifications
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  sim_fw_subset_subsumed:                 2
% 7.39/1.50  sim_bw_subset_subsumed:                 31
% 7.39/1.50  sim_fw_subsumed:                        6
% 7.39/1.50  sim_bw_subsumed:                        0
% 7.39/1.50  sim_fw_subsumption_res:                 0
% 7.39/1.50  sim_bw_subsumption_res:                 0
% 7.39/1.50  sim_tautology_del:                      0
% 7.39/1.50  sim_eq_tautology_del:                   0
% 7.39/1.50  sim_eq_res_simp:                        0
% 7.39/1.50  sim_fw_demodulated:                     0
% 7.39/1.50  sim_bw_demodulated:                     0
% 7.39/1.50  sim_light_normalised:                   8
% 7.39/1.50  sim_joinable_taut:                      0
% 7.39/1.50  sim_joinable_simp:                      0
% 7.39/1.50  sim_ac_normalised:                      0
% 7.39/1.50  sim_smt_subsumption:                    0
% 7.39/1.50  
%------------------------------------------------------------------------------
