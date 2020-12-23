%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:12 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 203 expanded)
%              Number of clauses        :   43 (  86 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  268 ( 658 expanded)
%              Number of equality atoms :  140 ( 341 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4) )
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).

fof(f37,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f20,f19,f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f25])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,
    ( k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_342,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_347,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_352,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_569,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_352])).

cnf(c_1561,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK1(X0,X1,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_347,c_569])).

cnf(c_15,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | v1_relat_1(X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_484,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_536,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_539,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_2867,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK1(X0,X1,k1_xboole_0)),X1) = iProver_top
    | k5_relat_1(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1561,c_15,c_484,c_539])).

cnf(c_2868,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK1(X0,X1,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2867])).

cnf(c_2876,plain,
    ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2868,c_569])).

cnf(c_3086,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2876,c_15,c_484,c_539])).

cnf(c_3087,plain,
    ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3086])).

cnf(c_3092,plain,
    ( k5_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_342,c_3087])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_346,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1270,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK0(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_346,c_569])).

cnf(c_1931,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X0) = iProver_top
    | k5_relat_1(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1270,c_15,c_484,c_539])).

cnf(c_1932,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK0(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1931])).

cnf(c_1940,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1932,c_569])).

cnf(c_2113,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1940,c_15,c_484,c_539])).

cnf(c_2114,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2113])).

cnf(c_2119,plain,
    ( k5_relat_1(k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_342,c_2114])).

cnf(c_134,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_603,plain,
    ( k5_relat_1(k1_xboole_0,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_604,plain,
    ( k5_relat_1(k1_xboole_0,sK4) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_491,plain,
    ( k5_relat_1(sK4,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_492,plain,
    ( k5_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_45,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_44,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3092,c_2119,c_604,c_492,c_45,c_44,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.65/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.65/1.04  
% 0.65/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.65/1.04  
% 0.65/1.04  ------  iProver source info
% 0.65/1.04  
% 0.65/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.65/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.65/1.04  git: non_committed_changes: false
% 0.65/1.04  git: last_make_outside_of_git: false
% 0.65/1.04  
% 0.65/1.04  ------ 
% 0.65/1.04  
% 0.65/1.04  ------ Input Options
% 0.65/1.04  
% 0.65/1.04  --out_options                           all
% 0.65/1.04  --tptp_safe_out                         true
% 0.65/1.04  --problem_path                          ""
% 0.65/1.04  --include_path                          ""
% 0.65/1.04  --clausifier                            res/vclausify_rel
% 0.65/1.04  --clausifier_options                    --mode clausify
% 0.65/1.04  --stdin                                 false
% 0.65/1.04  --stats_out                             all
% 0.65/1.04  
% 0.65/1.04  ------ General Options
% 0.65/1.04  
% 0.65/1.04  --fof                                   false
% 0.65/1.04  --time_out_real                         305.
% 0.65/1.04  --time_out_virtual                      -1.
% 0.65/1.04  --symbol_type_check                     false
% 0.65/1.04  --clausify_out                          false
% 0.65/1.04  --sig_cnt_out                           false
% 0.65/1.04  --trig_cnt_out                          false
% 0.65/1.04  --trig_cnt_out_tolerance                1.
% 0.65/1.04  --trig_cnt_out_sk_spl                   false
% 0.65/1.04  --abstr_cl_out                          false
% 0.65/1.04  
% 0.65/1.04  ------ Global Options
% 0.65/1.04  
% 0.65/1.04  --schedule                              default
% 0.65/1.04  --add_important_lit                     false
% 0.65/1.04  --prop_solver_per_cl                    1000
% 0.65/1.04  --min_unsat_core                        false
% 0.65/1.04  --soft_assumptions                      false
% 0.65/1.04  --soft_lemma_size                       3
% 0.65/1.04  --prop_impl_unit_size                   0
% 0.65/1.04  --prop_impl_unit                        []
% 0.65/1.04  --share_sel_clauses                     true
% 0.65/1.04  --reset_solvers                         false
% 0.65/1.04  --bc_imp_inh                            [conj_cone]
% 0.65/1.04  --conj_cone_tolerance                   3.
% 0.65/1.04  --extra_neg_conj                        none
% 0.65/1.04  --large_theory_mode                     true
% 0.65/1.04  --prolific_symb_bound                   200
% 0.65/1.04  --lt_threshold                          2000
% 0.65/1.04  --clause_weak_htbl                      true
% 0.65/1.04  --gc_record_bc_elim                     false
% 0.65/1.04  
% 0.65/1.04  ------ Preprocessing Options
% 0.65/1.04  
% 0.65/1.04  --preprocessing_flag                    true
% 0.65/1.04  --time_out_prep_mult                    0.1
% 0.65/1.04  --splitting_mode                        input
% 0.65/1.04  --splitting_grd                         true
% 0.65/1.04  --splitting_cvd                         false
% 0.65/1.04  --splitting_cvd_svl                     false
% 0.65/1.04  --splitting_nvd                         32
% 0.65/1.04  --sub_typing                            true
% 0.65/1.04  --prep_gs_sim                           true
% 0.65/1.04  --prep_unflatten                        true
% 0.65/1.04  --prep_res_sim                          true
% 0.65/1.04  --prep_upred                            true
% 0.65/1.04  --prep_sem_filter                       exhaustive
% 0.65/1.04  --prep_sem_filter_out                   false
% 0.65/1.04  --pred_elim                             true
% 0.65/1.04  --res_sim_input                         true
% 0.65/1.04  --eq_ax_congr_red                       true
% 0.65/1.04  --pure_diseq_elim                       true
% 0.65/1.04  --brand_transform                       false
% 0.65/1.04  --non_eq_to_eq                          false
% 0.65/1.04  --prep_def_merge                        true
% 0.65/1.04  --prep_def_merge_prop_impl              false
% 0.65/1.04  --prep_def_merge_mbd                    true
% 0.65/1.04  --prep_def_merge_tr_red                 false
% 0.65/1.04  --prep_def_merge_tr_cl                  false
% 0.65/1.04  --smt_preprocessing                     true
% 0.65/1.04  --smt_ac_axioms                         fast
% 0.65/1.04  --preprocessed_out                      false
% 0.65/1.04  --preprocessed_stats                    false
% 0.65/1.04  
% 0.65/1.04  ------ Abstraction refinement Options
% 0.65/1.04  
% 0.65/1.04  --abstr_ref                             []
% 0.65/1.04  --abstr_ref_prep                        false
% 0.65/1.04  --abstr_ref_until_sat                   false
% 0.65/1.04  --abstr_ref_sig_restrict                funpre
% 0.65/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.65/1.04  --abstr_ref_under                       []
% 0.65/1.04  
% 0.65/1.04  ------ SAT Options
% 0.65/1.04  
% 0.65/1.04  --sat_mode                              false
% 0.65/1.04  --sat_fm_restart_options                ""
% 0.65/1.04  --sat_gr_def                            false
% 0.65/1.04  --sat_epr_types                         true
% 0.65/1.04  --sat_non_cyclic_types                  false
% 0.65/1.04  --sat_finite_models                     false
% 0.65/1.04  --sat_fm_lemmas                         false
% 0.65/1.04  --sat_fm_prep                           false
% 0.65/1.04  --sat_fm_uc_incr                        true
% 0.65/1.04  --sat_out_model                         small
% 0.65/1.04  --sat_out_clauses                       false
% 0.65/1.04  
% 0.65/1.04  ------ QBF Options
% 0.65/1.04  
% 0.65/1.04  --qbf_mode                              false
% 0.65/1.04  --qbf_elim_univ                         false
% 0.65/1.04  --qbf_dom_inst                          none
% 0.65/1.04  --qbf_dom_pre_inst                      false
% 0.65/1.04  --qbf_sk_in                             false
% 0.65/1.04  --qbf_pred_elim                         true
% 0.65/1.04  --qbf_split                             512
% 0.65/1.04  
% 0.65/1.04  ------ BMC1 Options
% 0.65/1.04  
% 0.65/1.04  --bmc1_incremental                      false
% 0.65/1.04  --bmc1_axioms                           reachable_all
% 0.65/1.04  --bmc1_min_bound                        0
% 0.65/1.04  --bmc1_max_bound                        -1
% 0.65/1.04  --bmc1_max_bound_default                -1
% 0.65/1.04  --bmc1_symbol_reachability              true
% 0.65/1.04  --bmc1_property_lemmas                  false
% 0.65/1.04  --bmc1_k_induction                      false
% 0.65/1.04  --bmc1_non_equiv_states                 false
% 0.65/1.04  --bmc1_deadlock                         false
% 0.65/1.04  --bmc1_ucm                              false
% 0.65/1.04  --bmc1_add_unsat_core                   none
% 0.65/1.04  --bmc1_unsat_core_children              false
% 0.65/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.65/1.04  --bmc1_out_stat                         full
% 0.65/1.04  --bmc1_ground_init                      false
% 0.65/1.04  --bmc1_pre_inst_next_state              false
% 0.65/1.04  --bmc1_pre_inst_state                   false
% 0.65/1.04  --bmc1_pre_inst_reach_state             false
% 0.65/1.04  --bmc1_out_unsat_core                   false
% 0.65/1.04  --bmc1_aig_witness_out                  false
% 0.65/1.04  --bmc1_verbose                          false
% 0.65/1.04  --bmc1_dump_clauses_tptp                false
% 0.65/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.65/1.04  --bmc1_dump_file                        -
% 0.65/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.65/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.65/1.04  --bmc1_ucm_extend_mode                  1
% 0.65/1.04  --bmc1_ucm_init_mode                    2
% 0.65/1.04  --bmc1_ucm_cone_mode                    none
% 0.65/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.65/1.04  --bmc1_ucm_relax_model                  4
% 0.65/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.65/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.65/1.04  --bmc1_ucm_layered_model                none
% 0.65/1.04  --bmc1_ucm_max_lemma_size               10
% 0.65/1.04  
% 0.65/1.04  ------ AIG Options
% 0.65/1.04  
% 0.65/1.04  --aig_mode                              false
% 0.65/1.04  
% 0.65/1.04  ------ Instantiation Options
% 0.65/1.04  
% 0.65/1.04  --instantiation_flag                    true
% 0.65/1.04  --inst_sos_flag                         false
% 0.65/1.04  --inst_sos_phase                        true
% 0.65/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.65/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.65/1.04  --inst_lit_sel_side                     num_symb
% 0.65/1.04  --inst_solver_per_active                1400
% 0.65/1.04  --inst_solver_calls_frac                1.
% 0.65/1.04  --inst_passive_queue_type               priority_queues
% 0.65/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.65/1.04  --inst_passive_queues_freq              [25;2]
% 0.65/1.04  --inst_dismatching                      true
% 0.65/1.04  --inst_eager_unprocessed_to_passive     true
% 0.65/1.04  --inst_prop_sim_given                   true
% 0.65/1.04  --inst_prop_sim_new                     false
% 0.65/1.04  --inst_subs_new                         false
% 0.65/1.04  --inst_eq_res_simp                      false
% 0.65/1.04  --inst_subs_given                       false
% 0.65/1.04  --inst_orphan_elimination               true
% 0.65/1.04  --inst_learning_loop_flag               true
% 0.65/1.04  --inst_learning_start                   3000
% 0.65/1.04  --inst_learning_factor                  2
% 0.65/1.04  --inst_start_prop_sim_after_learn       3
% 0.65/1.04  --inst_sel_renew                        solver
% 0.65/1.04  --inst_lit_activity_flag                true
% 0.65/1.04  --inst_restr_to_given                   false
% 0.65/1.04  --inst_activity_threshold               500
% 0.65/1.04  --inst_out_proof                        true
% 0.65/1.04  
% 0.65/1.04  ------ Resolution Options
% 0.65/1.04  
% 0.65/1.04  --resolution_flag                       true
% 0.65/1.04  --res_lit_sel                           adaptive
% 0.65/1.04  --res_lit_sel_side                      none
% 0.65/1.04  --res_ordering                          kbo
% 0.65/1.04  --res_to_prop_solver                    active
% 0.65/1.04  --res_prop_simpl_new                    false
% 0.65/1.04  --res_prop_simpl_given                  true
% 0.65/1.04  --res_passive_queue_type                priority_queues
% 0.65/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.65/1.04  --res_passive_queues_freq               [15;5]
% 0.65/1.04  --res_forward_subs                      full
% 0.65/1.04  --res_backward_subs                     full
% 0.65/1.04  --res_forward_subs_resolution           true
% 0.65/1.04  --res_backward_subs_resolution          true
% 0.65/1.04  --res_orphan_elimination                true
% 0.65/1.04  --res_time_limit                        2.
% 0.65/1.04  --res_out_proof                         true
% 0.65/1.04  
% 0.65/1.04  ------ Superposition Options
% 0.65/1.04  
% 0.65/1.04  --superposition_flag                    true
% 0.65/1.04  --sup_passive_queue_type                priority_queues
% 0.65/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.65/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.65/1.04  --demod_completeness_check              fast
% 0.65/1.04  --demod_use_ground                      true
% 0.65/1.04  --sup_to_prop_solver                    passive
% 0.65/1.04  --sup_prop_simpl_new                    true
% 0.65/1.04  --sup_prop_simpl_given                  true
% 0.65/1.04  --sup_fun_splitting                     false
% 0.65/1.04  --sup_smt_interval                      50000
% 0.65/1.04  
% 0.65/1.04  ------ Superposition Simplification Setup
% 0.65/1.04  
% 0.65/1.04  --sup_indices_passive                   []
% 0.65/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.65/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.65/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.65/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.65/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.65/1.04  --sup_full_bw                           [BwDemod]
% 0.65/1.04  --sup_immed_triv                        [TrivRules]
% 0.65/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.65/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.65/1.04  --sup_immed_bw_main                     []
% 0.65/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.65/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.65/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.65/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.65/1.04  
% 0.65/1.04  ------ Combination Options
% 0.65/1.04  
% 0.65/1.04  --comb_res_mult                         3
% 0.65/1.04  --comb_sup_mult                         2
% 0.65/1.04  --comb_inst_mult                        10
% 0.65/1.04  
% 0.65/1.04  ------ Debug Options
% 0.65/1.04  
% 0.65/1.04  --dbg_backtrace                         false
% 0.65/1.04  --dbg_dump_prop_clauses                 false
% 0.65/1.04  --dbg_dump_prop_clauses_file            -
% 0.65/1.04  --dbg_out_stat                          false
% 0.65/1.04  ------ Parsing...
% 0.65/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.65/1.04  
% 0.65/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.65/1.04  
% 0.65/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.65/1.04  
% 0.65/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.65/1.04  ------ Proving...
% 0.65/1.04  ------ Problem Properties 
% 0.65/1.04  
% 0.65/1.04  
% 0.65/1.04  clauses                                 15
% 0.65/1.04  conjectures                             2
% 0.65/1.04  EPR                                     1
% 0.65/1.04  Horn                                    12
% 0.65/1.04  unary                                   5
% 0.65/1.04  binary                                  1
% 0.65/1.04  lits                                    51
% 0.65/1.04  lits eq                                 10
% 0.65/1.04  fd_pure                                 0
% 0.65/1.04  fd_pseudo                               0
% 0.65/1.04  fd_cond                                 1
% 0.65/1.04  fd_pseudo_cond                          3
% 0.65/1.04  AC symbols                              0
% 0.65/1.04  
% 0.65/1.04  ------ Schedule dynamic 5 is on 
% 0.65/1.04  
% 0.65/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.65/1.04  
% 0.65/1.04  
% 0.65/1.04  ------ 
% 0.65/1.04  Current options:
% 0.65/1.04  ------ 
% 0.65/1.04  
% 0.65/1.04  ------ Input Options
% 0.65/1.04  
% 0.65/1.04  --out_options                           all
% 0.65/1.04  --tptp_safe_out                         true
% 0.65/1.04  --problem_path                          ""
% 0.65/1.04  --include_path                          ""
% 0.65/1.04  --clausifier                            res/vclausify_rel
% 0.65/1.04  --clausifier_options                    --mode clausify
% 0.65/1.04  --stdin                                 false
% 0.65/1.04  --stats_out                             all
% 0.65/1.04  
% 0.65/1.04  ------ General Options
% 0.65/1.04  
% 0.65/1.04  --fof                                   false
% 0.65/1.04  --time_out_real                         305.
% 0.65/1.04  --time_out_virtual                      -1.
% 0.65/1.04  --symbol_type_check                     false
% 0.65/1.04  --clausify_out                          false
% 0.65/1.04  --sig_cnt_out                           false
% 0.65/1.04  --trig_cnt_out                          false
% 0.65/1.04  --trig_cnt_out_tolerance                1.
% 0.65/1.04  --trig_cnt_out_sk_spl                   false
% 0.65/1.04  --abstr_cl_out                          false
% 0.65/1.04  
% 0.65/1.04  ------ Global Options
% 0.65/1.04  
% 0.65/1.04  --schedule                              default
% 0.65/1.04  --add_important_lit                     false
% 0.65/1.04  --prop_solver_per_cl                    1000
% 0.65/1.04  --min_unsat_core                        false
% 0.65/1.04  --soft_assumptions                      false
% 0.65/1.04  --soft_lemma_size                       3
% 0.65/1.04  --prop_impl_unit_size                   0
% 0.65/1.04  --prop_impl_unit                        []
% 0.65/1.04  --share_sel_clauses                     true
% 0.65/1.04  --reset_solvers                         false
% 0.65/1.04  --bc_imp_inh                            [conj_cone]
% 0.65/1.04  --conj_cone_tolerance                   3.
% 0.65/1.04  --extra_neg_conj                        none
% 0.65/1.04  --large_theory_mode                     true
% 0.65/1.04  --prolific_symb_bound                   200
% 0.65/1.04  --lt_threshold                          2000
% 0.65/1.04  --clause_weak_htbl                      true
% 0.65/1.04  --gc_record_bc_elim                     false
% 0.65/1.04  
% 0.65/1.04  ------ Preprocessing Options
% 0.65/1.04  
% 0.65/1.04  --preprocessing_flag                    true
% 0.65/1.04  --time_out_prep_mult                    0.1
% 0.65/1.04  --splitting_mode                        input
% 0.65/1.04  --splitting_grd                         true
% 0.65/1.04  --splitting_cvd                         false
% 0.65/1.04  --splitting_cvd_svl                     false
% 0.65/1.04  --splitting_nvd                         32
% 0.65/1.04  --sub_typing                            true
% 0.65/1.04  --prep_gs_sim                           true
% 0.65/1.04  --prep_unflatten                        true
% 0.65/1.04  --prep_res_sim                          true
% 0.65/1.04  --prep_upred                            true
% 0.65/1.04  --prep_sem_filter                       exhaustive
% 0.65/1.04  --prep_sem_filter_out                   false
% 0.65/1.04  --pred_elim                             true
% 0.65/1.04  --res_sim_input                         true
% 0.65/1.04  --eq_ax_congr_red                       true
% 0.65/1.04  --pure_diseq_elim                       true
% 0.65/1.04  --brand_transform                       false
% 0.65/1.04  --non_eq_to_eq                          false
% 0.65/1.04  --prep_def_merge                        true
% 0.65/1.04  --prep_def_merge_prop_impl              false
% 0.65/1.04  --prep_def_merge_mbd                    true
% 0.65/1.04  --prep_def_merge_tr_red                 false
% 0.65/1.04  --prep_def_merge_tr_cl                  false
% 0.65/1.04  --smt_preprocessing                     true
% 0.65/1.04  --smt_ac_axioms                         fast
% 0.65/1.04  --preprocessed_out                      false
% 0.65/1.04  --preprocessed_stats                    false
% 0.65/1.04  
% 0.65/1.04  ------ Abstraction refinement Options
% 0.65/1.04  
% 0.65/1.04  --abstr_ref                             []
% 0.65/1.04  --abstr_ref_prep                        false
% 0.65/1.04  --abstr_ref_until_sat                   false
% 0.65/1.04  --abstr_ref_sig_restrict                funpre
% 0.65/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.65/1.04  --abstr_ref_under                       []
% 0.65/1.04  
% 0.65/1.04  ------ SAT Options
% 0.65/1.04  
% 0.65/1.04  --sat_mode                              false
% 0.65/1.04  --sat_fm_restart_options                ""
% 0.65/1.04  --sat_gr_def                            false
% 0.65/1.04  --sat_epr_types                         true
% 0.65/1.04  --sat_non_cyclic_types                  false
% 0.65/1.04  --sat_finite_models                     false
% 0.65/1.04  --sat_fm_lemmas                         false
% 0.65/1.04  --sat_fm_prep                           false
% 0.65/1.04  --sat_fm_uc_incr                        true
% 0.65/1.04  --sat_out_model                         small
% 0.65/1.04  --sat_out_clauses                       false
% 0.65/1.04  
% 0.65/1.04  ------ QBF Options
% 0.65/1.04  
% 0.65/1.04  --qbf_mode                              false
% 0.65/1.04  --qbf_elim_univ                         false
% 0.65/1.04  --qbf_dom_inst                          none
% 0.65/1.04  --qbf_dom_pre_inst                      false
% 0.65/1.04  --qbf_sk_in                             false
% 0.65/1.04  --qbf_pred_elim                         true
% 0.65/1.04  --qbf_split                             512
% 0.65/1.04  
% 0.65/1.04  ------ BMC1 Options
% 0.65/1.04  
% 0.65/1.04  --bmc1_incremental                      false
% 0.65/1.04  --bmc1_axioms                           reachable_all
% 0.65/1.04  --bmc1_min_bound                        0
% 0.65/1.04  --bmc1_max_bound                        -1
% 0.65/1.04  --bmc1_max_bound_default                -1
% 0.65/1.04  --bmc1_symbol_reachability              true
% 0.65/1.04  --bmc1_property_lemmas                  false
% 0.65/1.04  --bmc1_k_induction                      false
% 0.65/1.04  --bmc1_non_equiv_states                 false
% 0.65/1.04  --bmc1_deadlock                         false
% 0.65/1.04  --bmc1_ucm                              false
% 0.65/1.04  --bmc1_add_unsat_core                   none
% 0.65/1.04  --bmc1_unsat_core_children              false
% 0.65/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.65/1.04  --bmc1_out_stat                         full
% 0.65/1.04  --bmc1_ground_init                      false
% 0.65/1.04  --bmc1_pre_inst_next_state              false
% 0.65/1.04  --bmc1_pre_inst_state                   false
% 0.65/1.04  --bmc1_pre_inst_reach_state             false
% 0.65/1.04  --bmc1_out_unsat_core                   false
% 0.65/1.04  --bmc1_aig_witness_out                  false
% 0.65/1.04  --bmc1_verbose                          false
% 0.65/1.04  --bmc1_dump_clauses_tptp                false
% 0.65/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.65/1.04  --bmc1_dump_file                        -
% 0.65/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.65/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.65/1.04  --bmc1_ucm_extend_mode                  1
% 0.65/1.04  --bmc1_ucm_init_mode                    2
% 0.65/1.04  --bmc1_ucm_cone_mode                    none
% 0.65/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.65/1.04  --bmc1_ucm_relax_model                  4
% 0.65/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.65/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.65/1.04  --bmc1_ucm_layered_model                none
% 0.65/1.04  --bmc1_ucm_max_lemma_size               10
% 0.65/1.04  
% 0.65/1.04  ------ AIG Options
% 0.65/1.04  
% 0.65/1.04  --aig_mode                              false
% 0.65/1.04  
% 0.65/1.04  ------ Instantiation Options
% 0.65/1.04  
% 0.65/1.04  --instantiation_flag                    true
% 0.65/1.04  --inst_sos_flag                         false
% 0.65/1.04  --inst_sos_phase                        true
% 0.65/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.65/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.65/1.04  --inst_lit_sel_side                     none
% 0.65/1.04  --inst_solver_per_active                1400
% 0.65/1.04  --inst_solver_calls_frac                1.
% 0.65/1.04  --inst_passive_queue_type               priority_queues
% 0.65/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.65/1.04  --inst_passive_queues_freq              [25;2]
% 0.65/1.04  --inst_dismatching                      true
% 0.65/1.04  --inst_eager_unprocessed_to_passive     true
% 0.65/1.04  --inst_prop_sim_given                   true
% 0.65/1.04  --inst_prop_sim_new                     false
% 0.65/1.04  --inst_subs_new                         false
% 0.65/1.04  --inst_eq_res_simp                      false
% 0.65/1.04  --inst_subs_given                       false
% 0.65/1.04  --inst_orphan_elimination               true
% 0.65/1.04  --inst_learning_loop_flag               true
% 0.65/1.04  --inst_learning_start                   3000
% 0.65/1.04  --inst_learning_factor                  2
% 0.65/1.04  --inst_start_prop_sim_after_learn       3
% 0.65/1.04  --inst_sel_renew                        solver
% 0.65/1.04  --inst_lit_activity_flag                true
% 0.65/1.04  --inst_restr_to_given                   false
% 0.65/1.04  --inst_activity_threshold               500
% 0.65/1.04  --inst_out_proof                        true
% 0.65/1.04  
% 0.65/1.04  ------ Resolution Options
% 0.65/1.04  
% 0.65/1.04  --resolution_flag                       false
% 0.65/1.04  --res_lit_sel                           adaptive
% 0.65/1.04  --res_lit_sel_side                      none
% 0.65/1.04  --res_ordering                          kbo
% 0.65/1.04  --res_to_prop_solver                    active
% 0.65/1.04  --res_prop_simpl_new                    false
% 0.65/1.04  --res_prop_simpl_given                  true
% 0.65/1.04  --res_passive_queue_type                priority_queues
% 0.65/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.65/1.04  --res_passive_queues_freq               [15;5]
% 0.65/1.04  --res_forward_subs                      full
% 0.65/1.04  --res_backward_subs                     full
% 0.65/1.04  --res_forward_subs_resolution           true
% 0.65/1.04  --res_backward_subs_resolution          true
% 0.65/1.04  --res_orphan_elimination                true
% 0.65/1.04  --res_time_limit                        2.
% 0.65/1.04  --res_out_proof                         true
% 0.65/1.04  
% 0.65/1.04  ------ Superposition Options
% 0.65/1.04  
% 0.65/1.04  --superposition_flag                    true
% 0.65/1.04  --sup_passive_queue_type                priority_queues
% 0.65/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.65/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.65/1.04  --demod_completeness_check              fast
% 0.65/1.04  --demod_use_ground                      true
% 0.65/1.04  --sup_to_prop_solver                    passive
% 0.65/1.04  --sup_prop_simpl_new                    true
% 0.65/1.04  --sup_prop_simpl_given                  true
% 0.65/1.04  --sup_fun_splitting                     false
% 0.65/1.04  --sup_smt_interval                      50000
% 0.65/1.04  
% 0.65/1.04  ------ Superposition Simplification Setup
% 0.65/1.04  
% 0.65/1.04  --sup_indices_passive                   []
% 0.65/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.65/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.65/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.65/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.65/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.65/1.04  --sup_full_bw                           [BwDemod]
% 0.65/1.04  --sup_immed_triv                        [TrivRules]
% 0.65/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.65/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.65/1.04  --sup_immed_bw_main                     []
% 0.65/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.65/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.65/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.65/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.65/1.04  
% 0.65/1.04  ------ Combination Options
% 0.65/1.04  
% 0.65/1.04  --comb_res_mult                         3
% 0.65/1.04  --comb_sup_mult                         2
% 0.65/1.04  --comb_inst_mult                        10
% 0.65/1.04  
% 0.65/1.04  ------ Debug Options
% 0.65/1.04  
% 0.65/1.04  --dbg_backtrace                         false
% 0.65/1.04  --dbg_dump_prop_clauses                 false
% 0.65/1.04  --dbg_dump_prop_clauses_file            -
% 0.65/1.04  --dbg_out_stat                          false
% 0.65/1.04  
% 0.65/1.04  
% 0.65/1.04  
% 0.65/1.04  
% 0.65/1.04  ------ Proving...
% 0.65/1.04  
% 0.65/1.04  
% 0.65/1.04  % SZS status Theorem for theBenchmark.p
% 0.65/1.04  
% 0.65/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.65/1.04  
% 0.65/1.04  fof(f7,conjecture,(
% 0.65/1.04    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.65/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.65/1.04  
% 0.65/1.04  fof(f8,negated_conjecture,(
% 0.65/1.04    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.65/1.04    inference(negated_conjecture,[],[f7])).
% 0.65/1.04  
% 0.65/1.04  fof(f13,plain,(
% 0.65/1.04    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.65/1.04    inference(ennf_transformation,[],[f8])).
% 0.65/1.04  
% 0.65/1.04  fof(f22,plain,(
% 0.65/1.04    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4)) & v1_relat_1(sK4))),
% 0.65/1.04    introduced(choice_axiom,[])).
% 0.65/1.04  
% 0.65/1.04  fof(f23,plain,(
% 0.65/1.04    (k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4)) & v1_relat_1(sK4)),
% 0.65/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f22])).
% 0.65/1.04  
% 0.65/1.04  fof(f37,plain,(
% 0.65/1.04    v1_relat_1(sK4)),
% 0.65/1.04    inference(cnf_transformation,[],[f23])).
% 0.65/1.04  
% 0.65/1.04  fof(f6,axiom,(
% 0.65/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.65/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.65/1.04  
% 0.65/1.04  fof(f12,plain,(
% 0.65/1.04    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.65/1.04    inference(ennf_transformation,[],[f6])).
% 0.65/1.04  
% 0.65/1.04  fof(f16,plain,(
% 0.65/1.04    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.65/1.04    inference(nnf_transformation,[],[f12])).
% 0.65/1.04  
% 0.65/1.04  fof(f17,plain,(
% 0.65/1.04    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.65/1.04    inference(rectify,[],[f16])).
% 0.65/1.04  
% 0.65/1.04  fof(f20,plain,(
% 0.65/1.04    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)))),
% 0.65/1.04    introduced(choice_axiom,[])).
% 0.65/1.04  
% 0.65/1.04  fof(f19,plain,(
% 0.65/1.04    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 0.65/1.04    introduced(choice_axiom,[])).
% 0.65/1.04  
% 0.65/1.04  fof(f18,plain,(
% 0.65/1.04    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 0.65/1.04    introduced(choice_axiom,[])).
% 0.65/1.04  
% 0.65/1.04  fof(f21,plain,(
% 0.65/1.04    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.65/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f20,f19,f18])).
% 0.65/1.04  
% 0.65/1.04  fof(f35,plain,(
% 0.65/1.04    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.65/1.04    inference(cnf_transformation,[],[f21])).
% 0.65/1.04  
% 0.65/1.04  fof(f1,axiom,(
% 0.65/1.04    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.65/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.65/1.04  
% 0.65/1.04  fof(f14,plain,(
% 0.65/1.04    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.65/1.04    inference(nnf_transformation,[],[f1])).
% 0.65/1.04  
% 0.65/1.04  fof(f15,plain,(
% 0.65/1.04    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.65/1.04    inference(flattening,[],[f14])).
% 0.65/1.04  
% 0.65/1.04  fof(f26,plain,(
% 0.65/1.04    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.65/1.04    inference(cnf_transformation,[],[f15])).
% 0.65/1.04  
% 0.65/1.04  fof(f39,plain,(
% 0.65/1.04    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 0.65/1.04    inference(equality_resolution,[],[f26])).
% 0.65/1.04  
% 0.65/1.04  fof(f2,axiom,(
% 0.65/1.04    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.65/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.65/1.04  
% 0.65/1.04  fof(f27,plain,(
% 0.65/1.04    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.65/1.04    inference(cnf_transformation,[],[f2])).
% 0.65/1.04  
% 0.65/1.04  fof(f5,axiom,(
% 0.65/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.65/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.65/1.04  
% 0.65/1.04  fof(f11,plain,(
% 0.65/1.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.65/1.04    inference(ennf_transformation,[],[f5])).
% 0.65/1.04  
% 0.65/1.04  fof(f30,plain,(
% 0.65/1.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.65/1.04    inference(cnf_transformation,[],[f11])).
% 0.65/1.04  
% 0.65/1.04  fof(f3,axiom,(
% 0.65/1.04    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.65/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.65/1.04  
% 0.65/1.04  fof(f28,plain,(
% 0.65/1.04    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.65/1.04    inference(cnf_transformation,[],[f3])).
% 0.65/1.04  
% 0.65/1.04  fof(f34,plain,(
% 0.65/1.04    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.65/1.04    inference(cnf_transformation,[],[f21])).
% 0.65/1.04  
% 0.65/1.04  fof(f25,plain,(
% 0.65/1.04    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.65/1.04    inference(cnf_transformation,[],[f15])).
% 0.65/1.04  
% 0.65/1.04  fof(f40,plain,(
% 0.65/1.04    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 0.65/1.04    inference(equality_resolution,[],[f25])).
% 0.65/1.04  
% 0.65/1.04  fof(f24,plain,(
% 0.65/1.04    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 0.65/1.04    inference(cnf_transformation,[],[f15])).
% 0.65/1.04  
% 0.65/1.04  fof(f38,plain,(
% 0.65/1.04    k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4)),
% 0.65/1.04    inference(cnf_transformation,[],[f23])).
% 0.65/1.04  
% 0.65/1.04  cnf(c_14,negated_conjecture,
% 0.65/1.04      ( v1_relat_1(sK4) ),
% 0.65/1.04      inference(cnf_transformation,[],[f37]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_342,plain,
% 0.65/1.04      ( v1_relat_1(sK4) = iProver_top ),
% 0.65/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_8,plain,
% 0.65/1.04      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
% 0.65/1.04      | ~ v1_relat_1(X0)
% 0.65/1.04      | ~ v1_relat_1(X1)
% 0.65/1.04      | ~ v1_relat_1(X2)
% 0.65/1.04      | k5_relat_1(X0,X1) = X2 ),
% 0.65/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_347,plain,
% 0.65/1.04      ( k5_relat_1(X0,X1) = X2
% 0.65/1.04      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) = iProver_top
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) = iProver_top
% 0.65/1.04      | v1_relat_1(X2) != iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.65/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_0,plain,
% 0.65/1.04      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.65/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_3,plain,
% 0.65/1.04      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 0.65/1.04      inference(cnf_transformation,[],[f27]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_352,plain,
% 0.65/1.04      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 0.65/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_569,plain,
% 0.65/1.04      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.65/1.04      inference(superposition,[status(thm)],[c_0,c_352]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_1561,plain,
% 0.65/1.04      ( k5_relat_1(X0,X1) = k1_xboole_0
% 0.65/1.04      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK1(X0,X1,k1_xboole_0)),X1) = iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(X1) != iProver_top
% 0.65/1.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.65/1.04      inference(superposition,[status(thm)],[c_347,c_569]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_15,plain,
% 0.65/1.04      ( v1_relat_1(sK4) = iProver_top ),
% 0.65/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_6,plain,
% 0.65/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.65/1.04      | ~ v1_relat_1(X1)
% 0.65/1.04      | v1_relat_1(X0) ),
% 0.65/1.04      inference(cnf_transformation,[],[f30]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_481,plain,
% 0.65/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
% 0.65/1.04      | v1_relat_1(X0)
% 0.65/1.04      | ~ v1_relat_1(sK4) ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_482,plain,
% 0.65/1.04      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 0.65/1.04      | v1_relat_1(X0) = iProver_top
% 0.65/1.04      | v1_relat_1(sK4) != iProver_top ),
% 0.65/1.04      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_484,plain,
% 0.65/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 0.65/1.04      | v1_relat_1(sK4) != iProver_top
% 0.65/1.04      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_482]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_4,plain,
% 0.65/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.65/1.04      inference(cnf_transformation,[],[f28]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_536,plain,
% 0.65/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_539,plain,
% 0.65/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 0.65/1.04      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_2867,plain,
% 0.65/1.04      ( v1_relat_1(X1) != iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK1(X0,X1,k1_xboole_0)),X1) = iProver_top
% 0.65/1.04      | k5_relat_1(X0,X1) = k1_xboole_0 ),
% 0.65/1.04      inference(global_propositional_subsumption,
% 0.65/1.04                [status(thm)],
% 0.65/1.04                [c_1561,c_15,c_484,c_539]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_2868,plain,
% 0.65/1.04      ( k5_relat_1(X0,X1) = k1_xboole_0
% 0.65/1.04      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK1(X0,X1,k1_xboole_0)),X1) = iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.65/1.04      inference(renaming,[status(thm)],[c_2867]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_2876,plain,
% 0.65/1.04      ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.65/1.04      inference(superposition,[status(thm)],[c_2868,c_569]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_3086,plain,
% 0.65/1.04      ( v1_relat_1(X0) != iProver_top
% 0.65/1.04      | k5_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.65/1.04      inference(global_propositional_subsumption,
% 0.65/1.04                [status(thm)],
% 0.65/1.04                [c_2876,c_15,c_484,c_539]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_3087,plain,
% 0.65/1.04      ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 0.65/1.04      | v1_relat_1(X0) != iProver_top ),
% 0.65/1.04      inference(renaming,[status(thm)],[c_3086]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_3092,plain,
% 0.65/1.04      ( k5_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 0.65/1.04      inference(superposition,[status(thm)],[c_342,c_3087]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_9,plain,
% 0.65/1.04      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
% 0.65/1.04      | ~ v1_relat_1(X0)
% 0.65/1.04      | ~ v1_relat_1(X1)
% 0.65/1.04      | ~ v1_relat_1(X2)
% 0.65/1.04      | k5_relat_1(X0,X1) = X2 ),
% 0.65/1.04      inference(cnf_transformation,[],[f34]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_346,plain,
% 0.65/1.04      ( k5_relat_1(X0,X1) = X2
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) = iProver_top
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) = iProver_top
% 0.65/1.04      | v1_relat_1(X2) != iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.65/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_1270,plain,
% 0.65/1.04      ( k5_relat_1(X0,X1) = k1_xboole_0
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X0) = iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(X1) != iProver_top
% 0.65/1.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.65/1.04      inference(superposition,[status(thm)],[c_346,c_569]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_1931,plain,
% 0.65/1.04      ( v1_relat_1(X1) != iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X0) = iProver_top
% 0.65/1.04      | k5_relat_1(X0,X1) = k1_xboole_0 ),
% 0.65/1.04      inference(global_propositional_subsumption,
% 0.65/1.04                [status(thm)],
% 0.65/1.04                [c_1270,c_15,c_484,c_539]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_1932,plain,
% 0.65/1.04      ( k5_relat_1(X0,X1) = k1_xboole_0
% 0.65/1.04      | r2_hidden(k4_tarski(sK0(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X0) = iProver_top
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.65/1.04      inference(renaming,[status(thm)],[c_1931]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_1940,plain,
% 0.65/1.04      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 0.65/1.04      | v1_relat_1(X0) != iProver_top
% 0.65/1.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.65/1.04      inference(superposition,[status(thm)],[c_1932,c_569]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_2113,plain,
% 0.65/1.04      ( v1_relat_1(X0) != iProver_top
% 0.65/1.04      | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.65/1.04      inference(global_propositional_subsumption,
% 0.65/1.04                [status(thm)],
% 0.65/1.04                [c_1940,c_15,c_484,c_539]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_2114,plain,
% 0.65/1.04      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 0.65/1.04      | v1_relat_1(X0) != iProver_top ),
% 0.65/1.04      inference(renaming,[status(thm)],[c_2113]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_2119,plain,
% 0.65/1.04      ( k5_relat_1(k1_xboole_0,sK4) = k1_xboole_0 ),
% 0.65/1.04      inference(superposition,[status(thm)],[c_342,c_2114]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_134,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_603,plain,
% 0.65/1.04      ( k5_relat_1(k1_xboole_0,sK4) != X0
% 0.65/1.04      | k1_xboole_0 != X0
% 0.65/1.04      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK4) ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_134]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_604,plain,
% 0.65/1.04      ( k5_relat_1(k1_xboole_0,sK4) != k1_xboole_0
% 0.65/1.04      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK4)
% 0.65/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_603]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_491,plain,
% 0.65/1.04      ( k5_relat_1(sK4,k1_xboole_0) != X0
% 0.65/1.04      | k1_xboole_0 != X0
% 0.65/1.04      | k1_xboole_0 = k5_relat_1(sK4,k1_xboole_0) ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_134]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_492,plain,
% 0.65/1.04      ( k5_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 0.65/1.04      | k1_xboole_0 = k5_relat_1(sK4,k1_xboole_0)
% 0.65/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_491]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_1,plain,
% 0.65/1.04      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.65/1.04      inference(cnf_transformation,[],[f40]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_45,plain,
% 0.65/1.04      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_2,plain,
% 0.65/1.04      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 0.65/1.04      | k1_xboole_0 = X1
% 0.65/1.04      | k1_xboole_0 = X0 ),
% 0.65/1.04      inference(cnf_transformation,[],[f24]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_44,plain,
% 0.65/1.04      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 0.65/1.04      | k1_xboole_0 = k1_xboole_0 ),
% 0.65/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(c_13,negated_conjecture,
% 0.65/1.04      ( k1_xboole_0 != k5_relat_1(sK4,k1_xboole_0)
% 0.65/1.04      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK4) ),
% 0.65/1.04      inference(cnf_transformation,[],[f38]) ).
% 0.65/1.04  
% 0.65/1.04  cnf(contradiction,plain,
% 0.65/1.04      ( $false ),
% 0.65/1.04      inference(minisat,
% 0.65/1.04                [status(thm)],
% 0.65/1.04                [c_3092,c_2119,c_604,c_492,c_45,c_44,c_13]) ).
% 0.65/1.04  
% 0.65/1.04  
% 0.65/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.65/1.04  
% 0.65/1.04  ------                               Statistics
% 0.65/1.05  
% 0.65/1.05  ------ General
% 0.65/1.05  
% 0.65/1.05  abstr_ref_over_cycles:                  0
% 0.65/1.05  abstr_ref_under_cycles:                 0
% 0.65/1.05  gc_basic_clause_elim:                   0
% 0.65/1.05  forced_gc_time:                         0
% 0.65/1.05  parsing_time:                           0.005
% 0.65/1.05  unif_index_cands_time:                  0.
% 0.65/1.05  unif_index_add_time:                    0.
% 0.65/1.05  orderings_time:                         0.
% 0.65/1.05  out_proof_time:                         0.007
% 0.65/1.05  total_time:                             0.096
% 0.65/1.05  num_of_symbols:                         44
% 0.65/1.05  num_of_terms:                           3633
% 0.65/1.05  
% 0.65/1.05  ------ Preprocessing
% 0.65/1.05  
% 0.65/1.05  num_of_splits:                          0
% 0.65/1.05  num_of_split_atoms:                     0
% 0.65/1.05  num_of_reused_defs:                     0
% 0.65/1.05  num_eq_ax_congr_red:                    28
% 0.65/1.05  num_of_sem_filtered_clauses:            1
% 0.65/1.05  num_of_subtypes:                        0
% 0.65/1.05  monotx_restored_types:                  0
% 0.65/1.05  sat_num_of_epr_types:                   0
% 0.65/1.05  sat_num_of_non_cyclic_types:            0
% 0.65/1.05  sat_guarded_non_collapsed_types:        0
% 0.65/1.05  num_pure_diseq_elim:                    0
% 0.65/1.05  simp_replaced_by:                       0
% 0.65/1.05  res_preprocessed:                       62
% 0.65/1.05  prep_upred:                             0
% 0.65/1.05  prep_unflattend:                        0
% 0.65/1.05  smt_new_axioms:                         0
% 0.65/1.05  pred_elim_cands:                        3
% 0.65/1.05  pred_elim:                              0
% 0.65/1.05  pred_elim_cl:                           0
% 0.65/1.05  pred_elim_cycles:                       1
% 0.65/1.05  merged_defs:                            0
% 0.65/1.05  merged_defs_ncl:                        0
% 0.65/1.05  bin_hyper_res:                          0
% 0.65/1.05  prep_cycles:                            3
% 0.65/1.05  pred_elim_time:                         0.
% 0.65/1.05  splitting_time:                         0.
% 0.65/1.05  sem_filter_time:                        0.
% 0.65/1.05  monotx_time:                            0.
% 0.65/1.05  subtype_inf_time:                       0.
% 0.65/1.05  
% 0.65/1.05  ------ Problem properties
% 0.65/1.05  
% 0.65/1.05  clauses:                                15
% 0.65/1.05  conjectures:                            2
% 0.65/1.05  epr:                                    1
% 0.65/1.05  horn:                                   12
% 0.65/1.05  ground:                                 2
% 0.65/1.05  unary:                                  5
% 0.65/1.05  binary:                                 1
% 0.65/1.05  lits:                                   51
% 0.65/1.05  lits_eq:                                10
% 0.65/1.05  fd_pure:                                0
% 0.65/1.05  fd_pseudo:                              0
% 0.65/1.05  fd_cond:                                1
% 0.65/1.05  fd_pseudo_cond:                         3
% 0.65/1.05  ac_symbols:                             0
% 0.65/1.05  
% 0.65/1.05  ------ Propositional Solver
% 0.65/1.05  
% 0.65/1.05  prop_solver_calls:                      24
% 0.65/1.05  prop_fast_solver_calls:                 566
% 0.65/1.05  smt_solver_calls:                       0
% 0.65/1.05  smt_fast_solver_calls:                  0
% 0.65/1.05  prop_num_of_clauses:                    833
% 0.65/1.05  prop_preprocess_simplified:             2529
% 0.65/1.05  prop_fo_subsumed:                       8
% 0.65/1.05  prop_solver_time:                       0.
% 0.65/1.05  smt_solver_time:                        0.
% 0.65/1.05  smt_fast_solver_time:                   0.
% 0.65/1.05  prop_fast_solver_time:                  0.
% 0.65/1.05  prop_unsat_core_time:                   0.
% 0.65/1.05  
% 0.65/1.05  ------ QBF
% 0.65/1.05  
% 0.65/1.05  qbf_q_res:                              0
% 0.65/1.05  qbf_num_tautologies:                    0
% 0.65/1.05  qbf_prep_cycles:                        0
% 0.65/1.05  
% 0.65/1.05  ------ BMC1
% 0.65/1.05  
% 0.65/1.05  bmc1_current_bound:                     -1
% 0.65/1.05  bmc1_last_solved_bound:                 -1
% 0.65/1.05  bmc1_unsat_core_size:                   -1
% 0.65/1.05  bmc1_unsat_core_parents_size:           -1
% 0.65/1.05  bmc1_merge_next_fun:                    0
% 0.65/1.05  bmc1_unsat_core_clauses_time:           0.
% 0.65/1.05  
% 0.65/1.05  ------ Instantiation
% 0.65/1.05  
% 0.65/1.05  inst_num_of_clauses:                    221
% 0.65/1.05  inst_num_in_passive:                    65
% 0.65/1.05  inst_num_in_active:                     138
% 0.65/1.05  inst_num_in_unprocessed:                18
% 0.65/1.05  inst_num_of_loops:                      190
% 0.65/1.05  inst_num_of_learning_restarts:          0
% 0.65/1.05  inst_num_moves_active_passive:          49
% 0.65/1.05  inst_lit_activity:                      0
% 0.65/1.05  inst_lit_activity_moves:                0
% 0.65/1.05  inst_num_tautologies:                   0
% 0.65/1.05  inst_num_prop_implied:                  0
% 0.65/1.05  inst_num_existing_simplified:           0
% 0.65/1.05  inst_num_eq_res_simplified:             0
% 0.65/1.05  inst_num_child_elim:                    0
% 0.65/1.05  inst_num_of_dismatching_blockings:      98
% 0.65/1.05  inst_num_of_non_proper_insts:           211
% 0.65/1.05  inst_num_of_duplicates:                 0
% 0.65/1.05  inst_inst_num_from_inst_to_res:         0
% 0.65/1.05  inst_dismatching_checking_time:         0.
% 0.65/1.05  
% 0.65/1.05  ------ Resolution
% 0.65/1.05  
% 0.65/1.05  res_num_of_clauses:                     0
% 0.65/1.05  res_num_in_passive:                     0
% 0.65/1.05  res_num_in_active:                      0
% 0.65/1.05  res_num_of_loops:                       65
% 0.65/1.05  res_forward_subset_subsumed:            9
% 0.65/1.05  res_backward_subset_subsumed:           0
% 0.65/1.05  res_forward_subsumed:                   0
% 0.65/1.05  res_backward_subsumed:                  0
% 0.65/1.05  res_forward_subsumption_resolution:     0
% 0.65/1.05  res_backward_subsumption_resolution:    0
% 0.65/1.05  res_clause_to_clause_subsumption:       306
% 0.65/1.05  res_orphan_elimination:                 0
% 0.65/1.05  res_tautology_del:                      15
% 0.65/1.05  res_num_eq_res_simplified:              0
% 0.65/1.05  res_num_sel_changes:                    0
% 0.65/1.05  res_moves_from_active_to_pass:          0
% 0.65/1.05  
% 0.65/1.05  ------ Superposition
% 0.65/1.05  
% 0.65/1.05  sup_time_total:                         0.
% 0.65/1.05  sup_time_generating:                    0.
% 0.65/1.05  sup_time_sim_full:                      0.
% 0.65/1.05  sup_time_sim_immed:                     0.
% 0.65/1.05  
% 0.65/1.05  sup_num_of_clauses:                     103
% 0.65/1.05  sup_num_in_active:                      36
% 0.65/1.05  sup_num_in_passive:                     67
% 0.65/1.05  sup_num_of_loops:                       36
% 0.65/1.05  sup_fw_superposition:                   43
% 0.65/1.05  sup_bw_superposition:                   70
% 0.65/1.05  sup_immediate_simplified:               17
% 0.65/1.05  sup_given_eliminated:                   0
% 0.65/1.05  comparisons_done:                       0
% 0.65/1.05  comparisons_avoided:                    0
% 0.65/1.05  
% 0.65/1.05  ------ Simplifications
% 0.65/1.05  
% 0.65/1.05  
% 0.65/1.05  sim_fw_subset_subsumed:                 1
% 0.65/1.05  sim_bw_subset_subsumed:                 0
% 0.65/1.05  sim_fw_subsumed:                        12
% 0.65/1.05  sim_bw_subsumed:                        1
% 0.65/1.05  sim_fw_subsumption_res:                 0
% 0.65/1.05  sim_bw_subsumption_res:                 0
% 0.65/1.05  sim_tautology_del:                      0
% 0.65/1.05  sim_eq_tautology_del:                   1
% 0.65/1.05  sim_eq_res_simp:                        1
% 0.65/1.05  sim_fw_demodulated:                     0
% 0.65/1.05  sim_bw_demodulated:                     1
% 0.65/1.05  sim_light_normalised:                   14
% 0.65/1.05  sim_joinable_taut:                      0
% 0.65/1.05  sim_joinable_simp:                      0
% 0.65/1.05  sim_ac_normalised:                      0
% 0.65/1.05  sim_smt_subsumption:                    0
% 0.65/1.05  
%------------------------------------------------------------------------------
