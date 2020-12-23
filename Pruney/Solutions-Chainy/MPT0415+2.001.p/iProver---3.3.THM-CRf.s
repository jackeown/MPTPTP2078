%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:12 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 935 expanded)
%              Number of clauses        :   71 ( 289 expanded)
%              Number of leaves         :   17 ( 190 expanded)
%              Depth                    :   26
%              Number of atoms          :  365 (3395 expanded)
%              Number of equality atoms :  207 (1690 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | r2_hidden(sK0(X0,X1,X2),X2) )
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | r2_hidden(sK0(X0,X1,X2),X2) )
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,X1) = X2
      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK1,sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_xboole_0 = k7_setfam_1(sK1,sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f55,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f36,f44,f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_494,plain,
    ( k7_setfam_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(sK0(X1,X2,X0),X0)
    | r2_hidden(k3_subset_1(X1,sK0(X1,X2,X0)),X2)
    | k7_setfam_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_495,plain,
    ( k7_setfam_1(X0,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_489,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_493,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_491,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_575,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_493,c_491])).

cnf(c_3611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_575])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3611,c_17])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_499,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_797,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_499])).

cnf(c_4031,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3633,c_797])).

cnf(c_7762,plain,
    ( k7_setfam_1(sK1,sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_495,c_4031])).

cnf(c_7874,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7762,c_17])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8012,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | k1_xboole_0 = X0
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7874,c_20])).

cnf(c_8013,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8012])).

cnf(c_8020,plain,
    ( k7_setfam_1(sK1,sK2) = X0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_8013])).

cnf(c_8035,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8020,c_17])).

cnf(c_8145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | k1_xboole_0 = X0
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8035,c_20])).

cnf(c_8146,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8145])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_490,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_490])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k6_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_498,plain,
    ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1652,plain,
    ( k3_subset_1(sK1,X0) = k6_subset_1(sK1,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_498])).

cnf(c_8156,plain,
    ( k3_subset_1(sK1,sK0(sK1,sK2,sK2)) = k6_subset_1(sK1,sK0(sK1,sK2,sK2))
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8146,c_1652])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_55,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_269,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_654,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_655,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_9690,plain,
    ( k3_subset_1(sK1,sK0(sK1,sK2,sK2)) = k6_subset_1(sK1,sK0(sK1,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8156,c_20,c_18,c_55,c_56,c_655])).

cnf(c_9694,plain,
    ( k7_setfam_1(sK1,sK2) = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
    | r2_hidden(k6_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9690,c_495])).

cnf(c_9704,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
    | r2_hidden(k6_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9694,c_17])).

cnf(c_9695,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k6_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9690,c_4031])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_15,c_0])).

cnf(c_488,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_14,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_524,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_488,c_14])).

cnf(c_1444,plain,
    ( k1_setfam_1(k2_tarski(X0,sK1)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_524])).

cnf(c_8157,plain,
    ( k1_setfam_1(k2_tarski(sK0(sK1,sK2,sK2),sK1)) = sK0(sK1,sK2,sK2)
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8146,c_1444])).

cnf(c_9220,plain,
    ( k1_setfam_1(k2_tarski(sK0(sK1,sK2,sK2),sK1)) = sK0(sK1,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8157,c_20,c_18,c_55,c_56,c_655])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_497,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1649,plain,
    ( k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_497,c_498])).

cnf(c_1672,plain,
    ( k3_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1649,c_14])).

cnf(c_4039,plain,
    ( m1_subset_1(k6_subset_1(sK1,X0),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k1_setfam_1(k2_tarski(sK1,X0)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_4031])).

cnf(c_2220,plain,
    ( m1_subset_1(k6_subset_1(sK1,X0),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2221,plain,
    ( m1_subset_1(k6_subset_1(sK1,X0),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2220])).

cnf(c_4044,plain,
    ( r2_hidden(k1_setfam_1(k2_tarski(sK1,X0)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4039,c_2221])).

cnf(c_4052,plain,
    ( r2_hidden(k1_setfam_1(k2_tarski(X0,sK1)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_4044])).

cnf(c_9239,plain,
    ( r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9220,c_4052])).

cnf(c_915,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_497])).

cnf(c_1323,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_915])).

cnf(c_9230,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9220,c_1323])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9704,c_9695,c_9239,c_9230,c_655,c_56,c_55,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.50/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.99  
% 3.50/0.99  ------  iProver source info
% 3.50/0.99  
% 3.50/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.99  git: non_committed_changes: false
% 3.50/0.99  git: last_make_outside_of_git: false
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options
% 3.50/0.99  
% 3.50/0.99  --out_options                           all
% 3.50/0.99  --tptp_safe_out                         true
% 3.50/0.99  --problem_path                          ""
% 3.50/0.99  --include_path                          ""
% 3.50/0.99  --clausifier                            res/vclausify_rel
% 3.50/0.99  --clausifier_options                    --mode clausify
% 3.50/0.99  --stdin                                 false
% 3.50/0.99  --stats_out                             all
% 3.50/0.99  
% 3.50/0.99  ------ General Options
% 3.50/0.99  
% 3.50/0.99  --fof                                   false
% 3.50/0.99  --time_out_real                         305.
% 3.50/0.99  --time_out_virtual                      -1.
% 3.50/0.99  --symbol_type_check                     false
% 3.50/0.99  --clausify_out                          false
% 3.50/0.99  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     num_symb
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       true
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  ------ Parsing...
% 3.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.99  ------ Proving...
% 3.50/0.99  ------ Problem Properties 
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  clauses                                 19
% 3.50/0.99  conjectures                             3
% 3.50/0.99  EPR                                     1
% 3.50/0.99  Horn                                    16
% 3.50/0.99  unary                                   9
% 3.50/0.99  binary                                  3
% 3.50/0.99  lits                                    45
% 3.50/0.99  lits eq                                 14
% 3.50/0.99  fd_pure                                 0
% 3.50/0.99  fd_pseudo                               0
% 3.50/0.99  fd_cond                                 1
% 3.50/0.99  fd_pseudo_cond                          3
% 3.50/0.99  AC symbols                              0
% 3.50/0.99  
% 3.50/0.99  ------ Schedule dynamic 5 is on 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  Current options:
% 3.50/0.99  ------ 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options
% 3.50/0.99  
% 3.50/0.99  --out_options                           all
% 3.50/0.99  --tptp_safe_out                         true
% 3.50/0.99  --problem_path                          ""
% 3.50/0.99  --include_path                          ""
% 3.50/0.99  --clausifier                            res/vclausify_rel
% 3.50/0.99  --clausifier_options                    --mode clausify
% 3.50/0.99  --stdin                                 false
% 3.50/0.99  --stats_out                             all
% 3.50/0.99  
% 3.50/0.99  ------ General Options
% 3.50/0.99  
% 3.50/0.99  --fof                                   false
% 3.50/0.99  --time_out_real                         305.
% 3.50/0.99  --time_out_virtual                      -1.
% 3.50/0.99  --symbol_type_check                     false
% 3.50/0.99  --clausify_out                          false
% 3.50/0.99  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     none
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       false
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f9,axiom,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(ennf_transformation,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(nnf_transformation,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(flattening,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(rectify,[],[f29])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0))) => ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ! [X0,X1] : (! [X2] : (((k7_setfam_1(X0,X1) = X2 | ((~r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1)) & (r2_hidden(k3_subset_1(X0,X4),X1) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | k7_setfam_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f47,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f32])).
% 3.50/0.99  
% 3.50/0.99  fof(f48,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k7_setfam_1(X0,X1) = X2 | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f32])).
% 3.50/0.99  
% 3.50/0.99  fof(f14,conjecture,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f15,negated_conjecture,(
% 3.50/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 3.50/0.99    inference(negated_conjecture,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f24,plain,(
% 3.50/0.99    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(ennf_transformation,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(flattening,[],[f24])).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK1,sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    k1_xboole_0 = k7_setfam_1(sK1,sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f54,plain,(
% 3.50/0.99    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f46,plain,(
% 3.50/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f32])).
% 3.50/0.99  
% 3.50/0.99  fof(f63,plain,(
% 3.50/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k7_setfam_1(X0,X1)) | ~r2_hidden(k3_subset_1(X0,X4),X1) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.50/0.99    inference(equality_resolution,[],[f46])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,axiom,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.50/0.99    inference(ennf_transformation,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f50,plain,(
% 3.50/0.99    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f56,plain,(
% 3.50/0.99    k1_xboole_0 = k7_setfam_1(sK1,sK2)),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.50/0.99    inference(nnf_transformation,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.50/0.99    inference(flattening,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f40,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.50/0.99    inference(cnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f61,plain,(
% 3.50/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.50/0.99    inference(equality_resolution,[],[f40])).
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.50/0.99    inference(ennf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f23,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.50/0.99    inference(flattening,[],[f22])).
% 3.50/0.99  
% 3.50/0.99  fof(f53,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f23])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,axiom,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f42,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f44,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f59,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f42,f44])).
% 3.50/0.99  
% 3.50/0.99  fof(f55,plain,(
% 3.50/0.99    k1_xboole_0 != sK2),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.50/0.99    inference(cnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f39,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.50/0.99    inference(cnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f62,plain,(
% 3.50/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.50/0.99    inference(equality_resolution,[],[f39])).
% 3.50/0.99  
% 3.50/0.99  fof(f12,axiom,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.50/0.99    inference(unused_predicate_definition_removal,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.50/0.99    inference(ennf_transformation,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f52,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f17,plain,(
% 3.50/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.50/0.99    inference(ennf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f57,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f36,f44,f44])).
% 3.50/0.99  
% 3.50/0.99  fof(f58,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f35,f57])).
% 3.50/0.99  
% 3.50/0.99  fof(f11,axiom,(
% 3.50/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f51,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f60,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f51,f57])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f7,axiom,(
% 3.50/0.99    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f43,plain,(
% 3.50/0.99    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.50/0.99      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(X1))
% 3.50/0.99      | k7_setfam_1(X1,X2) = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_494,plain,
% 3.50/0.99      ( k7_setfam_1(X0,X1) = X2
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.50/0.99      | r2_hidden(sK0(X1,X2,X0),X0)
% 3.50/0.99      | r2_hidden(k3_subset_1(X1,sK0(X1,X2,X0)),X2)
% 3.50/0.99      | k7_setfam_1(X1,X2) = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_495,plain,
% 3.50/0.99      ( k7_setfam_1(X0,X1) = X2
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.50/0.99      | r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_19,negated_conjecture,
% 3.50/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_489,plain,
% 3.50/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.50/0.99      | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.50/0.99      | r2_hidden(X0,k7_setfam_1(X1,X2))
% 3.50/0.99      | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_493,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.50/0.99      | m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.50/0.99      | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
% 3.50/0.99      | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.50/0.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_491,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.50/0.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_575,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.50/0.99      | r2_hidden(X0,k7_setfam_1(X1,X2)) = iProver_top
% 3.50/0.99      | r2_hidden(k3_subset_1(X1,X0),X2) != iProver_top ),
% 3.50/0.99      inference(forward_subsumption_resolution,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_493,c_491]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3611,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
% 3.50/0.99      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_489,c_575]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_17,negated_conjecture,
% 3.50/0.99      ( k1_xboole_0 = k7_setfam_1(sK1,sK2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3633,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.50/0.99      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_3611,c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2,plain,
% 3.50/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_499,plain,
% 3.50/0.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_797,plain,
% 3.50/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2,c_499]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4031,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_3633,c_797]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7762,plain,
% 3.50/0.99      ( k7_setfam_1(sK1,sK2) = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_495,c_4031]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7874,plain,
% 3.50/0.99      ( k1_xboole_0 = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_7762,c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_20,plain,
% 3.50/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8012,plain,
% 3.50/0.99      ( m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | k1_xboole_0 = X0
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_7874,c_20]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8013,plain,
% 3.50/0.99      ( k1_xboole_0 = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_8012]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8020,plain,
% 3.50/0.99      ( k7_setfam_1(sK1,sK2) = X0
% 3.50/0.99      | k1_xboole_0 = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_494,c_8013]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8035,plain,
% 3.50/0.99      ( k1_xboole_0 = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_8020,c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8145,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | k1_xboole_0 = X0
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_8035,c_20]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8146,plain,
% 3.50/0.99      ( k1_xboole_0 = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,X0),X0) = iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_8145]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_16,plain,
% 3.50/0.99      ( m1_subset_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.50/0.99      | ~ r2_hidden(X0,X2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_490,plain,
% 3.50/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.50/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_897,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
% 3.50/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_489,c_490]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.50/0.99      | k3_subset_1(X1,X0) = k6_subset_1(X1,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_498,plain,
% 3.50/0.99      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1652,plain,
% 3.50/0.99      ( k3_subset_1(sK1,X0) = k6_subset_1(sK1,X0)
% 3.50/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_897,c_498]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8156,plain,
% 3.50/0.99      ( k3_subset_1(sK1,sK0(sK1,sK2,sK2)) = k6_subset_1(sK1,sK0(sK1,sK2,sK2))
% 3.50/0.99      | sK2 = k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_8146,c_1652]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_18,negated_conjecture,
% 3.50/0.99      ( k1_xboole_0 != sK2 ),
% 3.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4,plain,
% 3.50/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = X1
% 3.50/0.99      | k1_xboole_0 = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_55,plain,
% 3.50/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3,plain,
% 3.50/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_56,plain,
% 3.50/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_269,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_654,plain,
% 3.50/0.99      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_269]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_655,plain,
% 3.50/0.99      ( sK2 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK2
% 3.50/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_654]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9690,plain,
% 3.50/0.99      ( k3_subset_1(sK1,sK0(sK1,sK2,sK2)) = k6_subset_1(sK1,sK0(sK1,sK2,sK2)) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_8156,c_20,c_18,c_55,c_56,c_655]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9694,plain,
% 3.50/0.99      ( k7_setfam_1(sK1,sK2) = sK2
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
% 3.50/0.99      | r2_hidden(k6_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_9690,c_495]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9704,plain,
% 3.50/0.99      ( sK2 = k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.50/0.99      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
% 3.50/0.99      | r2_hidden(k6_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) = iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_9694,c_17]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9695,plain,
% 3.50/0.99      ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | r2_hidden(k6_subset_1(sK1,sK0(sK1,sK2,sK2)),sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_9690,c_4031]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_15,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_167,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.50/0.99      | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ),
% 3.50/0.99      inference(resolution,[status(thm)],[c_15,c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_488,plain,
% 3.50/0.99      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_14,plain,
% 3.50/0.99      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_524,plain,
% 3.50/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_488,c_14]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1444,plain,
% 3.50/0.99      ( k1_setfam_1(k2_tarski(X0,sK1)) = X0
% 3.50/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_897,c_524]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8157,plain,
% 3.50/0.99      ( k1_setfam_1(k2_tarski(sK0(sK1,sK2,sK2),sK1)) = sK0(sK1,sK2,sK2)
% 3.50/0.99      | sK2 = k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_8146,c_1444]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9220,plain,
% 3.50/0.99      ( k1_setfam_1(k2_tarski(sK0(sK1,sK2,sK2),sK1)) = sK0(sK1,sK2,sK2) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_8157,c_20,c_18,c_55,c_56,c_655]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1,plain,
% 3.50/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7,plain,
% 3.50/0.99      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_497,plain,
% 3.50/0.99      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1649,plain,
% 3.50/0.99      ( k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_497,c_498]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1672,plain,
% 3.50/0.99      ( k3_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_1649,c_14]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4039,plain,
% 3.50/0.99      ( m1_subset_1(k6_subset_1(sK1,X0),k1_zfmisc_1(sK1)) != iProver_top
% 3.50/0.99      | r2_hidden(k1_setfam_1(k2_tarski(sK1,X0)),sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1672,c_4031]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2220,plain,
% 3.50/0.99      ( m1_subset_1(k6_subset_1(sK1,X0),k1_zfmisc_1(sK1)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2221,plain,
% 3.50/0.99      ( m1_subset_1(k6_subset_1(sK1,X0),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2220]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4044,plain,
% 3.50/0.99      ( r2_hidden(k1_setfam_1(k2_tarski(sK1,X0)),sK2) != iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_4039,c_2221]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4052,plain,
% 3.50/0.99      ( r2_hidden(k1_setfam_1(k2_tarski(X0,sK1)),sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1,c_4044]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9239,plain,
% 3.50/0.99      ( r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_9220,c_4052]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_915,plain,
% 3.50/0.99      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_14,c_497]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1323,plain,
% 3.50/0.99      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1,c_915]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9230,plain,
% 3.50/0.99      ( m1_subset_1(sK0(sK1,sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_9220,c_1323]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(contradiction,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(minisat,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_9704,c_9695,c_9239,c_9230,c_655,c_56,c_55,c_18,c_20]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.01
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.01
% 3.50/0.99  total_time:                             0.341
% 3.50/0.99  num_of_symbols:                         45
% 3.50/0.99  num_of_terms:                           14611
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          0
% 3.50/0.99  num_of_split_atoms:                     0
% 3.50/0.99  num_of_reused_defs:                     0
% 3.50/0.99  num_eq_ax_congr_red:                    23
% 3.50/0.99  num_of_sem_filtered_clauses:            1
% 3.50/0.99  num_of_subtypes:                        0
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       98
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        0
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        2
% 3.50/0.99  pred_elim:                              1
% 3.50/0.99  pred_elim_cl:                           1
% 3.50/0.99  pred_elim_cycles:                       3
% 3.50/0.99  merged_defs:                            0
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          0
% 3.50/0.99  prep_cycles:                            4
% 3.50/0.99  pred_elim_time:                         0.
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                19
% 3.50/0.99  conjectures:                            3
% 3.50/0.99  epr:                                    1
% 3.50/0.99  horn:                                   16
% 3.50/0.99  ground:                                 3
% 3.50/0.99  unary:                                  9
% 3.50/0.99  binary:                                 3
% 3.50/0.99  lits:                                   45
% 3.50/0.99  lits_eq:                                14
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                1
% 3.50/0.99  fd_pseudo_cond:                         3
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      29
% 3.50/0.99  prop_fast_solver_calls:                 651
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    3577
% 3.50/0.99  prop_preprocess_simplified:             6165
% 3.50/0.99  prop_fo_subsumed:                       12
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    946
% 3.50/0.99  inst_num_in_passive:                    43
% 3.50/0.99  inst_num_in_active:                     482
% 3.50/0.99  inst_num_in_unprocessed:                421
% 3.50/0.99  inst_num_of_loops:                      530
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          45
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                0
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      903
% 3.50/0.99  inst_num_of_non_proper_insts:           826
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       102
% 3.50/0.99  res_forward_subset_subsumed:            63
% 3.50/0.99  res_backward_subset_subsumed:           2
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     0
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       1221
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      20
% 3.50/0.99  res_num_eq_res_simplified:              0
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     371
% 3.50/0.99  sup_num_in_active:                      95
% 3.50/0.99  sup_num_in_passive:                     276
% 3.50/0.99  sup_num_of_loops:                       104
% 3.50/0.99  sup_fw_superposition:                   262
% 3.50/0.99  sup_bw_superposition:                   550
% 3.50/0.99  sup_immediate_simplified:               398
% 3.50/0.99  sup_given_eliminated:                   0
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    0
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 7
% 3.50/0.99  sim_bw_subset_subsumed:                 1
% 3.50/0.99  sim_fw_subsumed:                        104
% 3.50/0.99  sim_bw_subsumed:                        3
% 3.50/0.99  sim_fw_subsumption_res:                 4
% 3.50/0.99  sim_bw_subsumption_res:                 0
% 3.50/0.99  sim_tautology_del:                      0
% 3.50/0.99  sim_eq_tautology_del:                   126
% 3.50/0.99  sim_eq_res_simp:                        0
% 3.50/0.99  sim_fw_demodulated:                     93
% 3.50/0.99  sim_bw_demodulated:                     21
% 3.50/0.99  sim_light_normalised:                   258
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------
