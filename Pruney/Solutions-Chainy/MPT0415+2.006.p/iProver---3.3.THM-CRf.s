%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:13 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 197 expanded)
%              Number of clauses        :   43 (  58 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  276 ( 475 expanded)
%              Number of equality atoms :  113 ( 223 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f29])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f38])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | r2_hidden(sK2(X0,X1,X2),X2) )
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f61,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_167,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_563,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_564,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_566,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_769,plain,
    ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_564,c_566])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_771,plain,
    ( k7_setfam_1(sK3,k1_xboole_0) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_769,c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_565,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,k7_setfam_1(X1,X0)) != iProver_top
    | r2_hidden(k3_subset_1(X1,X2),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_567,c_565])).

cnf(c_2294,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK3,k1_xboole_0)) != iProver_top
    | r2_hidden(k3_subset_1(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_631])).

cnf(c_2299,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k3_subset_1(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2294,c_771])).

cnf(c_16,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_691,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_782,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_785,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_2318,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k3_subset_1(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2299,c_16,c_785])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_573,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_575,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1022,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_563,c_575])).

cnf(c_1391,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_573,c_1022])).

cnf(c_1502,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_575])).

cnf(c_41,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1830,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_41])).

cnf(c_1831,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1830])).

cnf(c_2326,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2318,c_1831])).

cnf(c_2330,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_563,c_2326])).

cnf(c_317,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_703,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_704,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_316,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_333,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2330,c_704,c_333,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.82/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.82/0.98  
% 1.82/0.98  ------  iProver source info
% 1.82/0.98  
% 1.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.82/0.98  git: non_committed_changes: false
% 1.82/0.98  git: last_make_outside_of_git: false
% 1.82/0.98  
% 1.82/0.98  ------ 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options
% 1.82/0.98  
% 1.82/0.98  --out_options                           all
% 1.82/0.98  --tptp_safe_out                         true
% 1.82/0.98  --problem_path                          ""
% 1.82/0.98  --include_path                          ""
% 1.82/0.98  --clausifier                            res/vclausify_rel
% 1.82/0.98  --clausifier_options                    --mode clausify
% 1.82/0.98  --stdin                                 false
% 1.82/0.98  --stats_out                             all
% 1.82/0.98  
% 1.82/0.98  ------ General Options
% 1.82/0.98  
% 1.82/0.98  --fof                                   false
% 1.82/0.98  --time_out_real                         305.
% 1.82/0.98  --time_out_virtual                      -1.
% 1.82/0.98  --symbol_type_check                     false
% 1.82/0.98  --clausify_out                          false
% 1.82/0.98  --sig_cnt_out                           false
% 1.82/0.98  --trig_cnt_out                          false
% 1.82/0.98  --trig_cnt_out_tolerance                1.
% 1.82/0.98  --trig_cnt_out_sk_spl                   false
% 1.82/0.98  --abstr_cl_out                          false
% 1.82/0.98  
% 1.82/0.98  ------ Global Options
% 1.82/0.98  
% 1.82/0.98  --schedule                              default
% 1.82/0.98  --add_important_lit                     false
% 1.82/0.98  --prop_solver_per_cl                    1000
% 1.82/0.98  --min_unsat_core                        false
% 1.82/0.98  --soft_assumptions                      false
% 1.82/0.98  --soft_lemma_size                       3
% 1.82/0.98  --prop_impl_unit_size                   0
% 1.82/0.98  --prop_impl_unit                        []
% 1.82/0.98  --share_sel_clauses                     true
% 1.82/0.98  --reset_solvers                         false
% 1.82/0.98  --bc_imp_inh                            [conj_cone]
% 1.82/0.98  --conj_cone_tolerance                   3.
% 1.82/0.98  --extra_neg_conj                        none
% 1.82/0.98  --large_theory_mode                     true
% 1.82/0.98  --prolific_symb_bound                   200
% 1.82/0.98  --lt_threshold                          2000
% 1.82/0.98  --clause_weak_htbl                      true
% 1.82/0.98  --gc_record_bc_elim                     false
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing Options
% 1.82/0.98  
% 1.82/0.98  --preprocessing_flag                    true
% 1.82/0.98  --time_out_prep_mult                    0.1
% 1.82/0.98  --splitting_mode                        input
% 1.82/0.98  --splitting_grd                         true
% 1.82/0.98  --splitting_cvd                         false
% 1.82/0.98  --splitting_cvd_svl                     false
% 1.82/0.98  --splitting_nvd                         32
% 1.82/0.98  --sub_typing                            true
% 1.82/0.98  --prep_gs_sim                           true
% 1.82/0.98  --prep_unflatten                        true
% 1.82/0.98  --prep_res_sim                          true
% 1.82/0.98  --prep_upred                            true
% 1.82/0.98  --prep_sem_filter                       exhaustive
% 1.82/0.98  --prep_sem_filter_out                   false
% 1.82/0.98  --pred_elim                             true
% 1.82/0.98  --res_sim_input                         true
% 1.82/0.98  --eq_ax_congr_red                       true
% 1.82/0.98  --pure_diseq_elim                       true
% 1.82/0.98  --brand_transform                       false
% 1.82/0.98  --non_eq_to_eq                          false
% 1.82/0.98  --prep_def_merge                        true
% 1.82/0.98  --prep_def_merge_prop_impl              false
% 1.82/0.98  --prep_def_merge_mbd                    true
% 1.82/0.98  --prep_def_merge_tr_red                 false
% 1.82/0.98  --prep_def_merge_tr_cl                  false
% 1.82/0.98  --smt_preprocessing                     true
% 1.82/0.98  --smt_ac_axioms                         fast
% 1.82/0.98  --preprocessed_out                      false
% 1.82/0.98  --preprocessed_stats                    false
% 1.82/0.98  
% 1.82/0.98  ------ Abstraction refinement Options
% 1.82/0.98  
% 1.82/0.98  --abstr_ref                             []
% 1.82/0.98  --abstr_ref_prep                        false
% 1.82/0.98  --abstr_ref_until_sat                   false
% 1.82/0.98  --abstr_ref_sig_restrict                funpre
% 1.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.98  --abstr_ref_under                       []
% 1.82/0.98  
% 1.82/0.98  ------ SAT Options
% 1.82/0.98  
% 1.82/0.98  --sat_mode                              false
% 1.82/0.98  --sat_fm_restart_options                ""
% 1.82/0.98  --sat_gr_def                            false
% 1.82/0.98  --sat_epr_types                         true
% 1.82/0.98  --sat_non_cyclic_types                  false
% 1.82/0.98  --sat_finite_models                     false
% 1.82/0.98  --sat_fm_lemmas                         false
% 1.82/0.98  --sat_fm_prep                           false
% 1.82/0.98  --sat_fm_uc_incr                        true
% 1.82/0.98  --sat_out_model                         small
% 1.82/0.98  --sat_out_clauses                       false
% 1.82/0.98  
% 1.82/0.98  ------ QBF Options
% 1.82/0.98  
% 1.82/0.98  --qbf_mode                              false
% 1.82/0.98  --qbf_elim_univ                         false
% 1.82/0.98  --qbf_dom_inst                          none
% 1.82/0.98  --qbf_dom_pre_inst                      false
% 1.82/0.98  --qbf_sk_in                             false
% 1.82/0.98  --qbf_pred_elim                         true
% 1.82/0.98  --qbf_split                             512
% 1.82/0.98  
% 1.82/0.98  ------ BMC1 Options
% 1.82/0.98  
% 1.82/0.98  --bmc1_incremental                      false
% 1.82/0.98  --bmc1_axioms                           reachable_all
% 1.82/0.98  --bmc1_min_bound                        0
% 1.82/0.98  --bmc1_max_bound                        -1
% 1.82/0.98  --bmc1_max_bound_default                -1
% 1.82/0.98  --bmc1_symbol_reachability              true
% 1.82/0.98  --bmc1_property_lemmas                  false
% 1.82/0.98  --bmc1_k_induction                      false
% 1.82/0.98  --bmc1_non_equiv_states                 false
% 1.82/0.98  --bmc1_deadlock                         false
% 1.82/0.98  --bmc1_ucm                              false
% 1.82/0.98  --bmc1_add_unsat_core                   none
% 1.82/0.98  --bmc1_unsat_core_children              false
% 1.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.98  --bmc1_out_stat                         full
% 1.82/0.98  --bmc1_ground_init                      false
% 1.82/0.98  --bmc1_pre_inst_next_state              false
% 1.82/0.98  --bmc1_pre_inst_state                   false
% 1.82/0.98  --bmc1_pre_inst_reach_state             false
% 1.82/0.98  --bmc1_out_unsat_core                   false
% 1.82/0.98  --bmc1_aig_witness_out                  false
% 1.82/0.98  --bmc1_verbose                          false
% 1.82/0.98  --bmc1_dump_clauses_tptp                false
% 1.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.98  --bmc1_dump_file                        -
% 1.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.98  --bmc1_ucm_extend_mode                  1
% 1.82/0.98  --bmc1_ucm_init_mode                    2
% 1.82/0.98  --bmc1_ucm_cone_mode                    none
% 1.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.98  --bmc1_ucm_relax_model                  4
% 1.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.98  --bmc1_ucm_layered_model                none
% 1.82/0.98  --bmc1_ucm_max_lemma_size               10
% 1.82/0.98  
% 1.82/0.98  ------ AIG Options
% 1.82/0.98  
% 1.82/0.98  --aig_mode                              false
% 1.82/0.98  
% 1.82/0.98  ------ Instantiation Options
% 1.82/0.98  
% 1.82/0.98  --instantiation_flag                    true
% 1.82/0.98  --inst_sos_flag                         false
% 1.82/0.98  --inst_sos_phase                        true
% 1.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel_side                     num_symb
% 1.82/0.98  --inst_solver_per_active                1400
% 1.82/0.98  --inst_solver_calls_frac                1.
% 1.82/0.98  --inst_passive_queue_type               priority_queues
% 1.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.98  --inst_passive_queues_freq              [25;2]
% 1.82/0.98  --inst_dismatching                      true
% 1.82/0.98  --inst_eager_unprocessed_to_passive     true
% 1.82/0.98  --inst_prop_sim_given                   true
% 1.82/0.98  --inst_prop_sim_new                     false
% 1.82/0.98  --inst_subs_new                         false
% 1.82/0.98  --inst_eq_res_simp                      false
% 1.82/0.98  --inst_subs_given                       false
% 1.82/0.98  --inst_orphan_elimination               true
% 1.82/0.98  --inst_learning_loop_flag               true
% 1.82/0.98  --inst_learning_start                   3000
% 1.82/0.98  --inst_learning_factor                  2
% 1.82/0.98  --inst_start_prop_sim_after_learn       3
% 1.82/0.98  --inst_sel_renew                        solver
% 1.82/0.98  --inst_lit_activity_flag                true
% 1.82/0.98  --inst_restr_to_given                   false
% 1.82/0.98  --inst_activity_threshold               500
% 1.82/0.98  --inst_out_proof                        true
% 1.82/0.98  
% 1.82/0.98  ------ Resolution Options
% 1.82/0.98  
% 1.82/0.98  --resolution_flag                       true
% 1.82/0.98  --res_lit_sel                           adaptive
% 1.82/0.98  --res_lit_sel_side                      none
% 1.82/0.98  --res_ordering                          kbo
% 1.82/0.98  --res_to_prop_solver                    active
% 1.82/0.98  --res_prop_simpl_new                    false
% 1.82/0.98  --res_prop_simpl_given                  true
% 1.82/0.98  --res_passive_queue_type                priority_queues
% 1.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.98  --res_passive_queues_freq               [15;5]
% 1.82/0.98  --res_forward_subs                      full
% 1.82/0.98  --res_backward_subs                     full
% 1.82/0.98  --res_forward_subs_resolution           true
% 1.82/0.98  --res_backward_subs_resolution          true
% 1.82/0.98  --res_orphan_elimination                true
% 1.82/0.98  --res_time_limit                        2.
% 1.82/0.98  --res_out_proof                         true
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Options
% 1.82/0.98  
% 1.82/0.98  --superposition_flag                    true
% 1.82/0.98  --sup_passive_queue_type                priority_queues
% 1.82/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.98  --demod_completeness_check              fast
% 1.82/0.98  --demod_use_ground                      true
% 1.82/0.98  --sup_to_prop_solver                    passive
% 1.82/0.98  --sup_prop_simpl_new                    true
% 1.82/0.98  --sup_prop_simpl_given                  true
% 1.82/0.98  --sup_fun_splitting                     false
% 1.82/0.98  --sup_smt_interval                      50000
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Simplification Setup
% 1.82/0.98  
% 1.82/0.98  --sup_indices_passive                   []
% 1.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_full_bw                           [BwDemod]
% 1.82/0.98  --sup_immed_triv                        [TrivRules]
% 1.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_immed_bw_main                     []
% 1.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  
% 1.82/0.98  ------ Combination Options
% 1.82/0.98  
% 1.82/0.98  --comb_res_mult                         3
% 1.82/0.98  --comb_sup_mult                         2
% 1.82/0.98  --comb_inst_mult                        10
% 1.82/0.98  
% 1.82/0.98  ------ Debug Options
% 1.82/0.98  
% 1.82/0.98  --dbg_backtrace                         false
% 1.82/0.98  --dbg_dump_prop_clauses                 false
% 1.82/0.98  --dbg_dump_prop_clauses_file            -
% 1.82/0.98  --dbg_out_stat                          false
% 1.82/0.98  ------ Parsing...
% 1.82/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.82/0.98  ------ Proving...
% 1.82/0.98  ------ Problem Properties 
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  clauses                                 15
% 1.82/0.98  conjectures                             3
% 1.82/0.98  EPR                                     2
% 1.82/0.98  Horn                                    11
% 1.82/0.98  unary                                   5
% 1.82/0.98  binary                                  4
% 1.82/0.98  lits                                    40
% 1.82/0.98  lits eq                                 7
% 1.82/0.98  fd_pure                                 0
% 1.82/0.98  fd_pseudo                               0
% 1.82/0.98  fd_cond                                 1
% 1.82/0.98  fd_pseudo_cond                          3
% 1.82/0.98  AC symbols                              0
% 1.82/0.98  
% 1.82/0.98  ------ Schedule dynamic 5 is on 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  ------ 
% 1.82/0.98  Current options:
% 1.82/0.98  ------ 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options
% 1.82/0.98  
% 1.82/0.98  --out_options                           all
% 1.82/0.98  --tptp_safe_out                         true
% 1.82/0.98  --problem_path                          ""
% 1.82/0.98  --include_path                          ""
% 1.82/0.98  --clausifier                            res/vclausify_rel
% 1.82/0.98  --clausifier_options                    --mode clausify
% 1.82/0.98  --stdin                                 false
% 1.82/0.98  --stats_out                             all
% 1.82/0.98  
% 1.82/0.98  ------ General Options
% 1.82/0.98  
% 1.82/0.98  --fof                                   false
% 1.82/0.98  --time_out_real                         305.
% 1.82/0.98  --time_out_virtual                      -1.
% 1.82/0.98  --symbol_type_check                     false
% 1.82/0.98  --clausify_out                          false
% 1.82/0.98  --sig_cnt_out                           false
% 1.82/0.98  --trig_cnt_out                          false
% 1.82/0.98  --trig_cnt_out_tolerance                1.
% 1.82/0.98  --trig_cnt_out_sk_spl                   false
% 1.82/0.98  --abstr_cl_out                          false
% 1.82/0.98  
% 1.82/0.98  ------ Global Options
% 1.82/0.98  
% 1.82/0.98  --schedule                              default
% 1.82/0.98  --add_important_lit                     false
% 1.82/0.98  --prop_solver_per_cl                    1000
% 1.82/0.98  --min_unsat_core                        false
% 1.82/0.98  --soft_assumptions                      false
% 1.82/0.98  --soft_lemma_size                       3
% 1.82/0.98  --prop_impl_unit_size                   0
% 1.82/0.98  --prop_impl_unit                        []
% 1.82/0.98  --share_sel_clauses                     true
% 1.82/0.98  --reset_solvers                         false
% 1.82/0.98  --bc_imp_inh                            [conj_cone]
% 1.82/0.98  --conj_cone_tolerance                   3.
% 1.82/0.98  --extra_neg_conj                        none
% 1.82/0.98  --large_theory_mode                     true
% 1.82/0.98  --prolific_symb_bound                   200
% 1.82/0.98  --lt_threshold                          2000
% 1.82/0.98  --clause_weak_htbl                      true
% 1.82/0.98  --gc_record_bc_elim                     false
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing Options
% 1.82/0.98  
% 1.82/0.98  --preprocessing_flag                    true
% 1.82/0.98  --time_out_prep_mult                    0.1
% 1.82/0.98  --splitting_mode                        input
% 1.82/0.98  --splitting_grd                         true
% 1.82/0.98  --splitting_cvd                         false
% 1.82/0.98  --splitting_cvd_svl                     false
% 1.82/0.98  --splitting_nvd                         32
% 1.82/0.98  --sub_typing                            true
% 1.82/0.98  --prep_gs_sim                           true
% 1.82/0.98  --prep_unflatten                        true
% 1.82/0.98  --prep_res_sim                          true
% 1.82/0.98  --prep_upred                            true
% 1.82/0.98  --prep_sem_filter                       exhaustive
% 1.82/0.98  --prep_sem_filter_out                   false
% 1.82/0.98  --pred_elim                             true
% 1.82/0.98  --res_sim_input                         true
% 1.82/0.98  --eq_ax_congr_red                       true
% 1.82/0.98  --pure_diseq_elim                       true
% 1.82/0.98  --brand_transform                       false
% 1.82/0.98  --non_eq_to_eq                          false
% 1.82/0.98  --prep_def_merge                        true
% 1.82/0.98  --prep_def_merge_prop_impl              false
% 1.82/0.98  --prep_def_merge_mbd                    true
% 1.82/0.98  --prep_def_merge_tr_red                 false
% 1.82/0.98  --prep_def_merge_tr_cl                  false
% 1.82/0.98  --smt_preprocessing                     true
% 1.82/0.98  --smt_ac_axioms                         fast
% 1.82/0.98  --preprocessed_out                      false
% 1.82/0.98  --preprocessed_stats                    false
% 1.82/0.98  
% 1.82/0.98  ------ Abstraction refinement Options
% 1.82/0.98  
% 1.82/0.98  --abstr_ref                             []
% 1.82/0.98  --abstr_ref_prep                        false
% 1.82/0.98  --abstr_ref_until_sat                   false
% 1.82/0.98  --abstr_ref_sig_restrict                funpre
% 1.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.98  --abstr_ref_under                       []
% 1.82/0.98  
% 1.82/0.98  ------ SAT Options
% 1.82/0.98  
% 1.82/0.98  --sat_mode                              false
% 1.82/0.98  --sat_fm_restart_options                ""
% 1.82/0.98  --sat_gr_def                            false
% 1.82/0.98  --sat_epr_types                         true
% 1.82/0.98  --sat_non_cyclic_types                  false
% 1.82/0.98  --sat_finite_models                     false
% 1.82/0.98  --sat_fm_lemmas                         false
% 1.82/0.98  --sat_fm_prep                           false
% 1.82/0.98  --sat_fm_uc_incr                        true
% 1.82/0.98  --sat_out_model                         small
% 1.82/0.98  --sat_out_clauses                       false
% 1.82/0.98  
% 1.82/0.98  ------ QBF Options
% 1.82/0.98  
% 1.82/0.98  --qbf_mode                              false
% 1.82/0.98  --qbf_elim_univ                         false
% 1.82/0.98  --qbf_dom_inst                          none
% 1.82/0.98  --qbf_dom_pre_inst                      false
% 1.82/0.98  --qbf_sk_in                             false
% 1.82/0.98  --qbf_pred_elim                         true
% 1.82/0.98  --qbf_split                             512
% 1.82/0.98  
% 1.82/0.98  ------ BMC1 Options
% 1.82/0.98  
% 1.82/0.98  --bmc1_incremental                      false
% 1.82/0.98  --bmc1_axioms                           reachable_all
% 1.82/0.98  --bmc1_min_bound                        0
% 1.82/0.98  --bmc1_max_bound                        -1
% 1.82/0.98  --bmc1_max_bound_default                -1
% 1.82/0.98  --bmc1_symbol_reachability              true
% 1.82/0.98  --bmc1_property_lemmas                  false
% 1.82/0.98  --bmc1_k_induction                      false
% 1.82/0.98  --bmc1_non_equiv_states                 false
% 1.82/0.98  --bmc1_deadlock                         false
% 1.82/0.98  --bmc1_ucm                              false
% 1.82/0.98  --bmc1_add_unsat_core                   none
% 1.82/0.98  --bmc1_unsat_core_children              false
% 1.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.98  --bmc1_out_stat                         full
% 1.82/0.98  --bmc1_ground_init                      false
% 1.82/0.98  --bmc1_pre_inst_next_state              false
% 1.82/0.98  --bmc1_pre_inst_state                   false
% 1.82/0.98  --bmc1_pre_inst_reach_state             false
% 1.82/0.98  --bmc1_out_unsat_core                   false
% 1.82/0.98  --bmc1_aig_witness_out                  false
% 1.82/0.98  --bmc1_verbose                          false
% 1.82/0.98  --bmc1_dump_clauses_tptp                false
% 1.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.98  --bmc1_dump_file                        -
% 1.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.98  --bmc1_ucm_extend_mode                  1
% 1.82/0.98  --bmc1_ucm_init_mode                    2
% 1.82/0.98  --bmc1_ucm_cone_mode                    none
% 1.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.98  --bmc1_ucm_relax_model                  4
% 1.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.98  --bmc1_ucm_layered_model                none
% 1.82/0.98  --bmc1_ucm_max_lemma_size               10
% 1.82/0.98  
% 1.82/0.98  ------ AIG Options
% 1.82/0.98  
% 1.82/0.98  --aig_mode                              false
% 1.82/0.98  
% 1.82/0.98  ------ Instantiation Options
% 1.82/0.98  
% 1.82/0.98  --instantiation_flag                    true
% 1.82/0.98  --inst_sos_flag                         false
% 1.82/0.98  --inst_sos_phase                        true
% 1.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel_side                     none
% 1.82/0.98  --inst_solver_per_active                1400
% 1.82/0.98  --inst_solver_calls_frac                1.
% 1.82/0.98  --inst_passive_queue_type               priority_queues
% 1.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.98  --inst_passive_queues_freq              [25;2]
% 1.82/0.98  --inst_dismatching                      true
% 1.82/0.98  --inst_eager_unprocessed_to_passive     true
% 1.82/0.98  --inst_prop_sim_given                   true
% 1.82/0.98  --inst_prop_sim_new                     false
% 1.82/0.98  --inst_subs_new                         false
% 1.82/0.98  --inst_eq_res_simp                      false
% 1.82/0.98  --inst_subs_given                       false
% 1.82/0.98  --inst_orphan_elimination               true
% 1.82/0.98  --inst_learning_loop_flag               true
% 1.82/0.98  --inst_learning_start                   3000
% 1.82/0.98  --inst_learning_factor                  2
% 1.82/0.98  --inst_start_prop_sim_after_learn       3
% 1.82/0.98  --inst_sel_renew                        solver
% 1.82/0.98  --inst_lit_activity_flag                true
% 1.82/0.98  --inst_restr_to_given                   false
% 1.82/0.98  --inst_activity_threshold               500
% 1.82/0.98  --inst_out_proof                        true
% 1.82/0.98  
% 1.82/0.98  ------ Resolution Options
% 1.82/0.98  
% 1.82/0.98  --resolution_flag                       false
% 1.82/0.98  --res_lit_sel                           adaptive
% 1.82/0.98  --res_lit_sel_side                      none
% 1.82/0.98  --res_ordering                          kbo
% 1.82/0.99  --res_to_prop_solver                    active
% 1.82/0.99  --res_prop_simpl_new                    false
% 1.82/0.99  --res_prop_simpl_given                  true
% 1.82/0.99  --res_passive_queue_type                priority_queues
% 1.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.99  --res_passive_queues_freq               [15;5]
% 1.82/0.99  --res_forward_subs                      full
% 1.82/0.99  --res_backward_subs                     full
% 1.82/0.99  --res_forward_subs_resolution           true
% 1.82/0.99  --res_backward_subs_resolution          true
% 1.82/0.99  --res_orphan_elimination                true
% 1.82/0.99  --res_time_limit                        2.
% 1.82/0.99  --res_out_proof                         true
% 1.82/0.99  
% 1.82/0.99  ------ Superposition Options
% 1.82/0.99  
% 1.82/0.99  --superposition_flag                    true
% 1.82/0.99  --sup_passive_queue_type                priority_queues
% 1.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.99  --demod_completeness_check              fast
% 1.82/0.99  --demod_use_ground                      true
% 1.82/0.99  --sup_to_prop_solver                    passive
% 1.82/0.99  --sup_prop_simpl_new                    true
% 1.82/0.99  --sup_prop_simpl_given                  true
% 1.82/0.99  --sup_fun_splitting                     false
% 1.82/0.99  --sup_smt_interval                      50000
% 1.82/0.99  
% 1.82/0.99  ------ Superposition Simplification Setup
% 1.82/0.99  
% 1.82/0.99  --sup_indices_passive                   []
% 1.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.99  --sup_full_bw                           [BwDemod]
% 1.82/0.99  --sup_immed_triv                        [TrivRules]
% 1.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.99  --sup_immed_bw_main                     []
% 1.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.99  
% 1.82/0.99  ------ Combination Options
% 1.82/0.99  
% 1.82/0.99  --comb_res_mult                         3
% 1.82/0.99  --comb_sup_mult                         2
% 1.82/0.99  --comb_inst_mult                        10
% 1.82/0.99  
% 1.82/0.99  ------ Debug Options
% 1.82/0.99  
% 1.82/0.99  --dbg_backtrace                         false
% 1.82/0.99  --dbg_dump_prop_clauses                 false
% 1.82/0.99  --dbg_dump_prop_clauses_file            -
% 1.82/0.99  --dbg_out_stat                          false
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  ------ Proving...
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  % SZS status Theorem for theBenchmark.p
% 1.82/0.99  
% 1.82/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.82/0.99  
% 1.82/0.99  fof(f1,axiom,(
% 1.82/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f19,plain,(
% 1.82/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.82/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 1.82/0.99  
% 1.82/0.99  fof(f20,plain,(
% 1.82/0.99    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.82/0.99    inference(ennf_transformation,[],[f19])).
% 1.82/0.99  
% 1.82/0.99  fof(f29,plain,(
% 1.82/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.82/0.99    introduced(choice_axiom,[])).
% 1.82/0.99  
% 1.82/0.99  fof(f30,plain,(
% 1.82/0.99    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 1.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f29])).
% 1.82/0.99  
% 1.82/0.99  fof(f40,plain,(
% 1.82/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f30])).
% 1.82/0.99  
% 1.82/0.99  fof(f2,axiom,(
% 1.82/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f21,plain,(
% 1.82/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.82/0.99    inference(ennf_transformation,[],[f2])).
% 1.82/0.99  
% 1.82/0.99  fof(f41,plain,(
% 1.82/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f21])).
% 1.82/0.99  
% 1.82/0.99  fof(f16,conjecture,(
% 1.82/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f17,negated_conjecture,(
% 1.82/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.82/0.99    inference(negated_conjecture,[],[f16])).
% 1.82/0.99  
% 1.82/0.99  fof(f27,plain,(
% 1.82/0.99    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(ennf_transformation,[],[f17])).
% 1.82/0.99  
% 1.82/0.99  fof(f28,plain,(
% 1.82/0.99    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(flattening,[],[f27])).
% 1.82/0.99  
% 1.82/0.99  fof(f38,plain,(
% 1.82/0.99    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 1.82/0.99    introduced(choice_axiom,[])).
% 1.82/0.99  
% 1.82/0.99  fof(f39,plain,(
% 1.82/0.99    k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 1.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f38])).
% 1.82/0.99  
% 1.82/0.99  fof(f60,plain,(
% 1.82/0.99    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 1.82/0.99    inference(cnf_transformation,[],[f39])).
% 1.82/0.99  
% 1.82/0.99  fof(f13,axiom,(
% 1.82/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f24,plain,(
% 1.82/0.99    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(ennf_transformation,[],[f13])).
% 1.82/0.99  
% 1.82/0.99  fof(f57,plain,(
% 1.82/0.99    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.82/0.99    inference(cnf_transformation,[],[f24])).
% 1.82/0.99  
% 1.82/0.99  fof(f62,plain,(
% 1.82/0.99    k1_xboole_0 = k7_setfam_1(sK3,sK4)),
% 1.82/0.99    inference(cnf_transformation,[],[f39])).
% 1.82/0.99  
% 1.82/0.99  fof(f12,axiom,(
% 1.82/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f23,plain,(
% 1.82/0.99    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(ennf_transformation,[],[f12])).
% 1.82/0.99  
% 1.82/0.99  fof(f33,plain,(
% 1.82/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(nnf_transformation,[],[f23])).
% 1.82/0.99  
% 1.82/0.99  fof(f34,plain,(
% 1.82/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(flattening,[],[f33])).
% 1.82/0.99  
% 1.82/0.99  fof(f35,plain,(
% 1.82/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(rectify,[],[f34])).
% 1.82/0.99  
% 1.82/0.99  fof(f36,plain,(
% 1.82/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))))),
% 1.82/0.99    introduced(choice_axiom,[])).
% 1.82/0.99  
% 1.82/0.99  fof(f37,plain,(
% 1.82/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 1.82/0.99  
% 1.82/0.99  fof(f52,plain,(
% 1.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.82/0.99    inference(cnf_transformation,[],[f37])).
% 1.82/0.99  
% 1.82/0.99  fof(f72,plain,(
% 1.82/0.99    ( ! [X4,X0,X1] : (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,k7_setfam_1(X0,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.82/0.99    inference(equality_resolution,[],[f52])).
% 1.82/0.99  
% 1.82/0.99  fof(f15,axiom,(
% 1.82/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f25,plain,(
% 1.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.82/0.99    inference(ennf_transformation,[],[f15])).
% 1.82/0.99  
% 1.82/0.99  fof(f26,plain,(
% 1.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.82/0.99    inference(flattening,[],[f25])).
% 1.82/0.99  
% 1.82/0.99  fof(f59,plain,(
% 1.82/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f26])).
% 1.82/0.99  
% 1.82/0.99  fof(f11,axiom,(
% 1.82/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f51,plain,(
% 1.82/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.82/0.99    inference(cnf_transformation,[],[f11])).
% 1.82/0.99  
% 1.82/0.99  fof(f4,axiom,(
% 1.82/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f44,plain,(
% 1.82/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f4])).
% 1.82/0.99  
% 1.82/0.99  fof(f3,axiom,(
% 1.82/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f18,plain,(
% 1.82/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.82/0.99    inference(rectify,[],[f3])).
% 1.82/0.99  
% 1.82/0.99  fof(f22,plain,(
% 1.82/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.82/0.99    inference(ennf_transformation,[],[f18])).
% 1.82/0.99  
% 1.82/0.99  fof(f31,plain,(
% 1.82/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 1.82/0.99    introduced(choice_axiom,[])).
% 1.82/0.99  
% 1.82/0.99  fof(f32,plain,(
% 1.82/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 1.82/0.99  
% 1.82/0.99  fof(f43,plain,(
% 1.82/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.82/0.99    inference(cnf_transformation,[],[f32])).
% 1.82/0.99  
% 1.82/0.99  fof(f14,axiom,(
% 1.82/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f58,plain,(
% 1.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.82/0.99    inference(cnf_transformation,[],[f14])).
% 1.82/0.99  
% 1.82/0.99  fof(f5,axiom,(
% 1.82/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f45,plain,(
% 1.82/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f5])).
% 1.82/0.99  
% 1.82/0.99  fof(f6,axiom,(
% 1.82/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f46,plain,(
% 1.82/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f6])).
% 1.82/0.99  
% 1.82/0.99  fof(f7,axiom,(
% 1.82/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f47,plain,(
% 1.82/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f7])).
% 1.82/0.99  
% 1.82/0.99  fof(f8,axiom,(
% 1.82/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f48,plain,(
% 1.82/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f8])).
% 1.82/0.99  
% 1.82/0.99  fof(f9,axiom,(
% 1.82/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f49,plain,(
% 1.82/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f9])).
% 1.82/0.99  
% 1.82/0.99  fof(f10,axiom,(
% 1.82/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/0.99  
% 1.82/0.99  fof(f50,plain,(
% 1.82/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.82/0.99    inference(cnf_transformation,[],[f10])).
% 1.82/0.99  
% 1.82/0.99  fof(f63,plain,(
% 1.82/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.99    inference(definition_unfolding,[],[f49,f50])).
% 1.82/0.99  
% 1.82/0.99  fof(f64,plain,(
% 1.82/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.82/0.99    inference(definition_unfolding,[],[f48,f63])).
% 1.82/0.99  
% 1.82/0.99  fof(f65,plain,(
% 1.82/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.82/0.99    inference(definition_unfolding,[],[f47,f64])).
% 1.82/0.99  
% 1.82/0.99  fof(f66,plain,(
% 1.82/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.82/0.99    inference(definition_unfolding,[],[f46,f65])).
% 1.82/0.99  
% 1.82/0.99  fof(f67,plain,(
% 1.82/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.82/0.99    inference(definition_unfolding,[],[f45,f66])).
% 1.82/0.99  
% 1.82/0.99  fof(f68,plain,(
% 1.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.82/0.99    inference(definition_unfolding,[],[f58,f67])).
% 1.82/0.99  
% 1.82/0.99  fof(f69,plain,(
% 1.82/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.82/0.99    inference(definition_unfolding,[],[f43,f68])).
% 1.82/0.99  
% 1.82/0.99  fof(f61,plain,(
% 1.82/0.99    k1_xboole_0 != sK4),
% 1.82/0.99    inference(cnf_transformation,[],[f39])).
% 1.82/0.99  
% 1.82/0.99  cnf(c_0,plain,
% 1.82/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.82/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1,plain,
% 1.82/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.82/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_167,plain,
% 1.82/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.82/0.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_563,plain,
% 1.82/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_15,negated_conjecture,
% 1.82/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 1.82/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_564,plain,
% 1.82/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_11,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.82/0.99      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 1.82/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_566,plain,
% 1.82/0.99      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 1.82/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_769,plain,
% 1.82/0.99      ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_564,c_566]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_13,negated_conjecture,
% 1.82/0.99      ( k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
% 1.82/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_771,plain,
% 1.82/0.99      ( k7_setfam_1(sK3,k1_xboole_0) = sK4 ),
% 1.82/0.99      inference(light_normalisation,[status(thm)],[c_769,c_13]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_10,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.82/0.99      | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.82/0.99      | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
% 1.82/0.99      | r2_hidden(k3_subset_1(X1,X0),X2) ),
% 1.82/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_567,plain,
% 1.82/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.82/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.82/0.99      | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.82/0.99      | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top
% 1.82/0.99      | r2_hidden(k3_subset_1(X1,X0),X2) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_12,plain,
% 1.82/0.99      ( m1_subset_1(X0,X1)
% 1.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.82/0.99      | ~ r2_hidden(X0,X2) ),
% 1.82/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_565,plain,
% 1.82/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 1.82/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 1.82/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_631,plain,
% 1.82/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.82/0.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.82/0.99      | r2_hidden(X2,k7_setfam_1(X1,X0)) != iProver_top
% 1.82/0.99      | r2_hidden(k3_subset_1(X1,X2),X0) = iProver_top ),
% 1.82/0.99      inference(forward_subsumption_resolution,
% 1.82/0.99                [status(thm)],
% 1.82/0.99                [c_567,c_565]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2294,plain,
% 1.82/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 1.82/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 1.82/0.99      | r2_hidden(X0,k7_setfam_1(sK3,k1_xboole_0)) != iProver_top
% 1.82/0.99      | r2_hidden(k3_subset_1(sK3,X0),k1_xboole_0) = iProver_top ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_771,c_631]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2299,plain,
% 1.82/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 1.82/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 1.82/0.99      | r2_hidden(X0,sK4) != iProver_top
% 1.82/0.99      | r2_hidden(k3_subset_1(sK3,X0),k1_xboole_0) = iProver_top ),
% 1.82/0.99      inference(light_normalisation,[status(thm)],[c_2294,c_771]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_16,plain,
% 1.82/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_5,plain,
% 1.82/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.82/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_691,plain,
% 1.82/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_782,plain,
% 1.82/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_785,plain,
% 1.82/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2318,plain,
% 1.82/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 1.82/0.99      | r2_hidden(k3_subset_1(sK3,X0),k1_xboole_0) = iProver_top ),
% 1.82/0.99      inference(global_propositional_subsumption,
% 1.82/0.99                [status(thm)],
% 1.82/0.99                [c_2299,c_16,c_785]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_4,plain,
% 1.82/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.82/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_573,plain,
% 1.82/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2,plain,
% 1.82/0.99      ( ~ r1_xboole_0(X0,X1)
% 1.82/0.99      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 1.82/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_575,plain,
% 1.82/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 1.82/0.99      | r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1022,plain,
% 1.82/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0
% 1.82/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_563,c_575]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1391,plain,
% 1.82/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_573,c_1022]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1502,plain,
% 1.82/0.99      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 1.82/0.99      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_1391,c_575]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_41,plain,
% 1.82/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1830,plain,
% 1.82/0.99      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 1.82/0.99      inference(global_propositional_subsumption,
% 1.82/0.99                [status(thm)],
% 1.82/0.99                [c_1502,c_41]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1831,plain,
% 1.82/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.82/0.99      inference(renaming,[status(thm)],[c_1830]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2326,plain,
% 1.82/0.99      ( r2_hidden(X0,sK4) != iProver_top ),
% 1.82/0.99      inference(forward_subsumption_resolution,
% 1.82/0.99                [status(thm)],
% 1.82/0.99                [c_2318,c_1831]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2330,plain,
% 1.82/0.99      ( sK4 = k1_xboole_0 ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_563,c_2326]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_317,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_703,plain,
% 1.82/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_317]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_704,plain,
% 1.82/0.99      ( sK4 != k1_xboole_0
% 1.82/0.99      | k1_xboole_0 = sK4
% 1.82/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_703]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_316,plain,( X0 = X0 ),theory(equality) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_333,plain,
% 1.82/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_316]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_14,negated_conjecture,
% 1.82/0.99      ( k1_xboole_0 != sK4 ),
% 1.82/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(contradiction,plain,
% 1.82/0.99      ( $false ),
% 1.82/0.99      inference(minisat,[status(thm)],[c_2330,c_704,c_333,c_14]) ).
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.82/0.99  
% 1.82/0.99  ------                               Statistics
% 1.82/0.99  
% 1.82/0.99  ------ General
% 1.82/0.99  
% 1.82/0.99  abstr_ref_over_cycles:                  0
% 1.82/0.99  abstr_ref_under_cycles:                 0
% 1.82/0.99  gc_basic_clause_elim:                   0
% 1.82/0.99  forced_gc_time:                         0
% 1.82/0.99  parsing_time:                           0.007
% 1.82/0.99  unif_index_cands_time:                  0.
% 1.82/0.99  unif_index_add_time:                    0.
% 1.82/0.99  orderings_time:                         0.
% 1.82/0.99  out_proof_time:                         0.008
% 1.82/0.99  total_time:                             0.104
% 1.82/0.99  num_of_symbols:                         46
% 1.82/0.99  num_of_terms:                           2122
% 1.82/0.99  
% 1.82/0.99  ------ Preprocessing
% 1.82/0.99  
% 1.82/0.99  num_of_splits:                          0
% 1.82/0.99  num_of_split_atoms:                     0
% 1.82/0.99  num_of_reused_defs:                     0
% 1.82/0.99  num_eq_ax_congr_red:                    49
% 1.82/0.99  num_of_sem_filtered_clauses:            1
% 1.82/0.99  num_of_subtypes:                        0
% 1.82/0.99  monotx_restored_types:                  0
% 1.82/0.99  sat_num_of_epr_types:                   0
% 1.82/0.99  sat_num_of_non_cyclic_types:            0
% 1.82/0.99  sat_guarded_non_collapsed_types:        0
% 1.82/0.99  num_pure_diseq_elim:                    0
% 1.82/0.99  simp_replaced_by:                       0
% 1.82/0.99  res_preprocessed:                       80
% 1.82/0.99  prep_upred:                             0
% 1.82/0.99  prep_unflattend:                        4
% 1.82/0.99  smt_new_axioms:                         0
% 1.82/0.99  pred_elim_cands:                        3
% 1.82/0.99  pred_elim:                              1
% 1.82/0.99  pred_elim_cl:                           1
% 1.82/0.99  pred_elim_cycles:                       3
% 1.82/0.99  merged_defs:                            0
% 1.82/0.99  merged_defs_ncl:                        0
% 1.82/0.99  bin_hyper_res:                          0
% 1.82/0.99  prep_cycles:                            4
% 1.82/0.99  pred_elim_time:                         0.001
% 1.82/0.99  splitting_time:                         0.
% 1.82/0.99  sem_filter_time:                        0.
% 1.82/0.99  monotx_time:                            0.
% 1.82/0.99  subtype_inf_time:                       0.
% 1.82/0.99  
% 1.82/0.99  ------ Problem properties
% 1.82/0.99  
% 1.82/0.99  clauses:                                15
% 1.82/0.99  conjectures:                            3
% 1.82/0.99  epr:                                    2
% 1.82/0.99  horn:                                   11
% 1.82/0.99  ground:                                 3
% 1.82/0.99  unary:                                  5
% 1.82/0.99  binary:                                 4
% 1.82/0.99  lits:                                   40
% 1.82/0.99  lits_eq:                                7
% 1.82/0.99  fd_pure:                                0
% 1.82/0.99  fd_pseudo:                              0
% 1.82/0.99  fd_cond:                                1
% 1.82/0.99  fd_pseudo_cond:                         3
% 1.82/0.99  ac_symbols:                             0
% 1.82/0.99  
% 1.82/0.99  ------ Propositional Solver
% 1.82/0.99  
% 1.82/0.99  prop_solver_calls:                      27
% 1.82/0.99  prop_fast_solver_calls:                 550
% 1.82/0.99  smt_solver_calls:                       0
% 1.82/0.99  smt_fast_solver_calls:                  0
% 1.82/0.99  prop_num_of_clauses:                    715
% 1.82/0.99  prop_preprocess_simplified:             2905
% 1.82/0.99  prop_fo_subsumed:                       11
% 1.82/0.99  prop_solver_time:                       0.
% 1.82/0.99  smt_solver_time:                        0.
% 1.82/0.99  smt_fast_solver_time:                   0.
% 1.82/0.99  prop_fast_solver_time:                  0.
% 1.82/0.99  prop_unsat_core_time:                   0.
% 1.82/0.99  
% 1.82/0.99  ------ QBF
% 1.82/0.99  
% 1.82/0.99  qbf_q_res:                              0
% 1.82/0.99  qbf_num_tautologies:                    0
% 1.82/0.99  qbf_prep_cycles:                        0
% 1.82/0.99  
% 1.82/0.99  ------ BMC1
% 1.82/0.99  
% 1.82/0.99  bmc1_current_bound:                     -1
% 1.82/0.99  bmc1_last_solved_bound:                 -1
% 1.82/0.99  bmc1_unsat_core_size:                   -1
% 1.82/0.99  bmc1_unsat_core_parents_size:           -1
% 1.82/0.99  bmc1_merge_next_fun:                    0
% 1.82/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.82/0.99  
% 1.82/0.99  ------ Instantiation
% 1.82/0.99  
% 1.82/0.99  inst_num_of_clauses:                    207
% 1.82/0.99  inst_num_in_passive:                    38
% 1.82/0.99  inst_num_in_active:                     140
% 1.82/0.99  inst_num_in_unprocessed:                29
% 1.82/0.99  inst_num_of_loops:                      170
% 1.82/0.99  inst_num_of_learning_restarts:          0
% 1.82/0.99  inst_num_moves_active_passive:          27
% 1.82/0.99  inst_lit_activity:                      0
% 1.82/0.99  inst_lit_activity_moves:                0
% 1.82/0.99  inst_num_tautologies:                   0
% 1.82/0.99  inst_num_prop_implied:                  0
% 1.82/0.99  inst_num_existing_simplified:           0
% 1.82/0.99  inst_num_eq_res_simplified:             0
% 1.82/0.99  inst_num_child_elim:                    0
% 1.82/0.99  inst_num_of_dismatching_blockings:      126
% 1.82/0.99  inst_num_of_non_proper_insts:           251
% 1.82/0.99  inst_num_of_duplicates:                 0
% 1.82/0.99  inst_inst_num_from_inst_to_res:         0
% 1.82/0.99  inst_dismatching_checking_time:         0.
% 1.82/0.99  
% 1.82/0.99  ------ Resolution
% 1.82/0.99  
% 1.82/0.99  res_num_of_clauses:                     0
% 1.82/0.99  res_num_in_passive:                     0
% 1.82/0.99  res_num_in_active:                      0
% 1.82/0.99  res_num_of_loops:                       84
% 1.82/0.99  res_forward_subset_subsumed:            17
% 1.82/0.99  res_backward_subset_subsumed:           0
% 1.82/0.99  res_forward_subsumed:                   0
% 1.82/0.99  res_backward_subsumed:                  0
% 1.82/0.99  res_forward_subsumption_resolution:     0
% 1.82/0.99  res_backward_subsumption_resolution:    0
% 1.82/0.99  res_clause_to_clause_subsumption:       132
% 1.82/0.99  res_orphan_elimination:                 0
% 1.82/0.99  res_tautology_del:                      10
% 1.82/0.99  res_num_eq_res_simplified:              0
% 1.82/0.99  res_num_sel_changes:                    0
% 1.82/0.99  res_moves_from_active_to_pass:          0
% 1.82/0.99  
% 1.82/0.99  ------ Superposition
% 1.82/0.99  
% 1.82/0.99  sup_time_total:                         0.
% 1.82/0.99  sup_time_generating:                    0.
% 1.82/0.99  sup_time_sim_full:                      0.
% 1.82/0.99  sup_time_sim_immed:                     0.
% 1.82/0.99  
% 1.82/0.99  sup_num_of_clauses:                     51
% 1.82/0.99  sup_num_in_active:                      34
% 1.82/0.99  sup_num_in_passive:                     17
% 1.82/0.99  sup_num_of_loops:                       33
% 1.82/0.99  sup_fw_superposition:                   32
% 1.82/0.99  sup_bw_superposition:                   24
% 1.82/0.99  sup_immediate_simplified:               14
% 1.82/0.99  sup_given_eliminated:                   1
% 1.82/0.99  comparisons_done:                       0
% 1.82/0.99  comparisons_avoided:                    0
% 1.82/0.99  
% 1.82/0.99  ------ Simplifications
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  sim_fw_subset_subsumed:                 2
% 1.82/0.99  sim_bw_subset_subsumed:                 2
% 1.82/0.99  sim_fw_subsumed:                        5
% 1.82/0.99  sim_bw_subsumed:                        2
% 1.82/0.99  sim_fw_subsumption_res:                 2
% 1.82/0.99  sim_bw_subsumption_res:                 0
% 1.82/0.99  sim_tautology_del:                      1
% 1.82/0.99  sim_eq_tautology_del:                   3
% 1.82/0.99  sim_eq_res_simp:                        0
% 1.82/0.99  sim_fw_demodulated:                     3
% 1.82/0.99  sim_bw_demodulated:                     4
% 1.82/0.99  sim_light_normalised:                   6
% 1.82/0.99  sim_joinable_taut:                      0
% 1.82/0.99  sim_joinable_simp:                      0
% 1.82/0.99  sim_ac_normalised:                      0
% 1.82/0.99  sim_smt_subsumption:                    0
% 1.82/0.99  
%------------------------------------------------------------------------------
