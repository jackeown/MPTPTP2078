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
% DateTime   : Thu Dec  3 11:59:52 EST 2020

% Result     : Theorem 15.38s
% Output     : CNFRefutation 15.38s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 149 expanded)
%              Number of clauses        :   44 (  66 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   20
%              Number of atoms          :  240 ( 427 expanded)
%              Number of equality atoms :   82 ( 139 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f29])).

fof(f50,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_780,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_290,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | k1_wellord2(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_291,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = k3_relat_1(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_17,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_115,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_795,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_291,c_115])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_781,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_904,plain,
    ( r1_tarski(k1_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_781])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_782,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_977,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_904,c_782])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_779,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1241,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_782])).

cnf(c_7946,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_781,c_1241])).

cnf(c_10899,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7946,c_781])).

cnf(c_11117,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_10899])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_281,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | k1_wellord2(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_282,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_773,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_976,plain,
    ( k2_xboole_0(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
    inference(superposition,[status(thm)],[c_773,c_782])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_783,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3046,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_783])).

cnf(c_67014,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11117,c_3046])).

cnf(c_67529,plain,
    ( k2_xboole_0(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0)))) = k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0))) ),
    inference(superposition,[status(thm)],[c_67014,c_782])).

cnf(c_72814,plain,
    ( r1_tarski(k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0))),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_67529,c_783])).

cnf(c_74639,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(k2_relat_1(k1_wellord2(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_72814])).

cnf(c_74731,plain,
    ( r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) = iProver_top
    | r1_tarski(k2_relat_1(k1_wellord2(sK2)),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74639])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_785,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_784,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1220,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_relat_1(k1_wellord2(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_784])).

cnf(c_3262,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_1220])).

cnf(c_3280,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(sK2)),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74731,c_3280,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.38/2.55  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.38/2.55  
% 15.38/2.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.38/2.55  
% 15.38/2.55  ------  iProver source info
% 15.38/2.55  
% 15.38/2.55  git: date: 2020-06-30 10:37:57 +0100
% 15.38/2.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.38/2.55  git: non_committed_changes: false
% 15.38/2.55  git: last_make_outside_of_git: false
% 15.38/2.55  
% 15.38/2.55  ------ 
% 15.38/2.55  
% 15.38/2.55  ------ Input Options
% 15.38/2.55  
% 15.38/2.55  --out_options                           all
% 15.38/2.55  --tptp_safe_out                         true
% 15.38/2.55  --problem_path                          ""
% 15.38/2.55  --include_path                          ""
% 15.38/2.55  --clausifier                            res/vclausify_rel
% 15.38/2.55  --clausifier_options                    --mode clausify
% 15.38/2.55  --stdin                                 false
% 15.38/2.55  --stats_out                             all
% 15.38/2.55  
% 15.38/2.55  ------ General Options
% 15.38/2.55  
% 15.38/2.55  --fof                                   false
% 15.38/2.55  --time_out_real                         305.
% 15.38/2.55  --time_out_virtual                      -1.
% 15.38/2.55  --symbol_type_check                     false
% 15.38/2.55  --clausify_out                          false
% 15.38/2.55  --sig_cnt_out                           false
% 15.38/2.55  --trig_cnt_out                          false
% 15.38/2.55  --trig_cnt_out_tolerance                1.
% 15.38/2.55  --trig_cnt_out_sk_spl                   false
% 15.38/2.55  --abstr_cl_out                          false
% 15.38/2.55  
% 15.38/2.55  ------ Global Options
% 15.38/2.55  
% 15.38/2.55  --schedule                              default
% 15.38/2.55  --add_important_lit                     false
% 15.38/2.55  --prop_solver_per_cl                    1000
% 15.38/2.55  --min_unsat_core                        false
% 15.38/2.55  --soft_assumptions                      false
% 15.38/2.55  --soft_lemma_size                       3
% 15.38/2.55  --prop_impl_unit_size                   0
% 15.38/2.55  --prop_impl_unit                        []
% 15.38/2.55  --share_sel_clauses                     true
% 15.38/2.55  --reset_solvers                         false
% 15.38/2.55  --bc_imp_inh                            [conj_cone]
% 15.38/2.55  --conj_cone_tolerance                   3.
% 15.38/2.55  --extra_neg_conj                        none
% 15.38/2.55  --large_theory_mode                     true
% 15.38/2.55  --prolific_symb_bound                   200
% 15.38/2.55  --lt_threshold                          2000
% 15.38/2.55  --clause_weak_htbl                      true
% 15.38/2.55  --gc_record_bc_elim                     false
% 15.38/2.55  
% 15.38/2.55  ------ Preprocessing Options
% 15.38/2.55  
% 15.38/2.55  --preprocessing_flag                    true
% 15.38/2.55  --time_out_prep_mult                    0.1
% 15.38/2.55  --splitting_mode                        input
% 15.38/2.55  --splitting_grd                         true
% 15.38/2.55  --splitting_cvd                         false
% 15.38/2.55  --splitting_cvd_svl                     false
% 15.38/2.55  --splitting_nvd                         32
% 15.38/2.55  --sub_typing                            true
% 15.38/2.55  --prep_gs_sim                           true
% 15.38/2.55  --prep_unflatten                        true
% 15.38/2.55  --prep_res_sim                          true
% 15.38/2.55  --prep_upred                            true
% 15.38/2.55  --prep_sem_filter                       exhaustive
% 15.38/2.55  --prep_sem_filter_out                   false
% 15.38/2.55  --pred_elim                             true
% 15.38/2.55  --res_sim_input                         true
% 15.38/2.55  --eq_ax_congr_red                       true
% 15.38/2.55  --pure_diseq_elim                       true
% 15.38/2.55  --brand_transform                       false
% 15.38/2.55  --non_eq_to_eq                          false
% 15.38/2.55  --prep_def_merge                        true
% 15.38/2.55  --prep_def_merge_prop_impl              false
% 15.38/2.55  --prep_def_merge_mbd                    true
% 15.38/2.55  --prep_def_merge_tr_red                 false
% 15.38/2.55  --prep_def_merge_tr_cl                  false
% 15.38/2.55  --smt_preprocessing                     true
% 15.38/2.55  --smt_ac_axioms                         fast
% 15.38/2.55  --preprocessed_out                      false
% 15.38/2.55  --preprocessed_stats                    false
% 15.38/2.55  
% 15.38/2.55  ------ Abstraction refinement Options
% 15.38/2.55  
% 15.38/2.55  --abstr_ref                             []
% 15.38/2.55  --abstr_ref_prep                        false
% 15.38/2.55  --abstr_ref_until_sat                   false
% 15.38/2.55  --abstr_ref_sig_restrict                funpre
% 15.38/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.38/2.55  --abstr_ref_under                       []
% 15.38/2.55  
% 15.38/2.55  ------ SAT Options
% 15.38/2.55  
% 15.38/2.55  --sat_mode                              false
% 15.38/2.55  --sat_fm_restart_options                ""
% 15.38/2.55  --sat_gr_def                            false
% 15.38/2.55  --sat_epr_types                         true
% 15.38/2.55  --sat_non_cyclic_types                  false
% 15.38/2.55  --sat_finite_models                     false
% 15.38/2.55  --sat_fm_lemmas                         false
% 15.38/2.55  --sat_fm_prep                           false
% 15.38/2.55  --sat_fm_uc_incr                        true
% 15.38/2.55  --sat_out_model                         small
% 15.38/2.55  --sat_out_clauses                       false
% 15.38/2.55  
% 15.38/2.55  ------ QBF Options
% 15.38/2.55  
% 15.38/2.55  --qbf_mode                              false
% 15.38/2.55  --qbf_elim_univ                         false
% 15.38/2.55  --qbf_dom_inst                          none
% 15.38/2.55  --qbf_dom_pre_inst                      false
% 15.38/2.55  --qbf_sk_in                             false
% 15.38/2.55  --qbf_pred_elim                         true
% 15.38/2.55  --qbf_split                             512
% 15.38/2.55  
% 15.38/2.55  ------ BMC1 Options
% 15.38/2.55  
% 15.38/2.55  --bmc1_incremental                      false
% 15.38/2.55  --bmc1_axioms                           reachable_all
% 15.38/2.55  --bmc1_min_bound                        0
% 15.38/2.55  --bmc1_max_bound                        -1
% 15.38/2.55  --bmc1_max_bound_default                -1
% 15.38/2.55  --bmc1_symbol_reachability              true
% 15.38/2.55  --bmc1_property_lemmas                  false
% 15.38/2.55  --bmc1_k_induction                      false
% 15.38/2.55  --bmc1_non_equiv_states                 false
% 15.38/2.55  --bmc1_deadlock                         false
% 15.38/2.55  --bmc1_ucm                              false
% 15.38/2.55  --bmc1_add_unsat_core                   none
% 15.38/2.55  --bmc1_unsat_core_children              false
% 15.38/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.38/2.55  --bmc1_out_stat                         full
% 15.38/2.55  --bmc1_ground_init                      false
% 15.38/2.55  --bmc1_pre_inst_next_state              false
% 15.38/2.55  --bmc1_pre_inst_state                   false
% 15.38/2.55  --bmc1_pre_inst_reach_state             false
% 15.38/2.55  --bmc1_out_unsat_core                   false
% 15.38/2.55  --bmc1_aig_witness_out                  false
% 15.38/2.55  --bmc1_verbose                          false
% 15.38/2.55  --bmc1_dump_clauses_tptp                false
% 15.38/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.38/2.55  --bmc1_dump_file                        -
% 15.38/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.38/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.38/2.55  --bmc1_ucm_extend_mode                  1
% 15.38/2.55  --bmc1_ucm_init_mode                    2
% 15.38/2.55  --bmc1_ucm_cone_mode                    none
% 15.38/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.38/2.55  --bmc1_ucm_relax_model                  4
% 15.38/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.38/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.38/2.55  --bmc1_ucm_layered_model                none
% 15.38/2.55  --bmc1_ucm_max_lemma_size               10
% 15.38/2.55  
% 15.38/2.55  ------ AIG Options
% 15.38/2.55  
% 15.38/2.55  --aig_mode                              false
% 15.38/2.55  
% 15.38/2.55  ------ Instantiation Options
% 15.38/2.55  
% 15.38/2.55  --instantiation_flag                    true
% 15.38/2.55  --inst_sos_flag                         false
% 15.38/2.55  --inst_sos_phase                        true
% 15.38/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.38/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.38/2.55  --inst_lit_sel_side                     num_symb
% 15.38/2.55  --inst_solver_per_active                1400
% 15.38/2.55  --inst_solver_calls_frac                1.
% 15.38/2.55  --inst_passive_queue_type               priority_queues
% 15.38/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.38/2.55  --inst_passive_queues_freq              [25;2]
% 15.38/2.55  --inst_dismatching                      true
% 15.38/2.55  --inst_eager_unprocessed_to_passive     true
% 15.38/2.55  --inst_prop_sim_given                   true
% 15.38/2.55  --inst_prop_sim_new                     false
% 15.38/2.55  --inst_subs_new                         false
% 15.38/2.55  --inst_eq_res_simp                      false
% 15.38/2.55  --inst_subs_given                       false
% 15.38/2.55  --inst_orphan_elimination               true
% 15.38/2.55  --inst_learning_loop_flag               true
% 15.38/2.55  --inst_learning_start                   3000
% 15.38/2.55  --inst_learning_factor                  2
% 15.38/2.55  --inst_start_prop_sim_after_learn       3
% 15.38/2.55  --inst_sel_renew                        solver
% 15.38/2.55  --inst_lit_activity_flag                true
% 15.38/2.55  --inst_restr_to_given                   false
% 15.38/2.55  --inst_activity_threshold               500
% 15.38/2.55  --inst_out_proof                        true
% 15.38/2.55  
% 15.38/2.55  ------ Resolution Options
% 15.38/2.55  
% 15.38/2.55  --resolution_flag                       true
% 15.38/2.55  --res_lit_sel                           adaptive
% 15.38/2.55  --res_lit_sel_side                      none
% 15.38/2.55  --res_ordering                          kbo
% 15.38/2.55  --res_to_prop_solver                    active
% 15.38/2.55  --res_prop_simpl_new                    false
% 15.38/2.55  --res_prop_simpl_given                  true
% 15.38/2.55  --res_passive_queue_type                priority_queues
% 15.38/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.38/2.55  --res_passive_queues_freq               [15;5]
% 15.38/2.55  --res_forward_subs                      full
% 15.38/2.55  --res_backward_subs                     full
% 15.38/2.55  --res_forward_subs_resolution           true
% 15.38/2.55  --res_backward_subs_resolution          true
% 15.38/2.55  --res_orphan_elimination                true
% 15.38/2.55  --res_time_limit                        2.
% 15.38/2.55  --res_out_proof                         true
% 15.38/2.55  
% 15.38/2.55  ------ Superposition Options
% 15.38/2.55  
% 15.38/2.55  --superposition_flag                    true
% 15.38/2.55  --sup_passive_queue_type                priority_queues
% 15.38/2.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.38/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.38/2.55  --demod_completeness_check              fast
% 15.38/2.55  --demod_use_ground                      true
% 15.38/2.55  --sup_to_prop_solver                    passive
% 15.38/2.55  --sup_prop_simpl_new                    true
% 15.38/2.55  --sup_prop_simpl_given                  true
% 15.38/2.55  --sup_fun_splitting                     false
% 15.38/2.55  --sup_smt_interval                      50000
% 15.38/2.55  
% 15.38/2.55  ------ Superposition Simplification Setup
% 15.38/2.55  
% 15.38/2.55  --sup_indices_passive                   []
% 15.38/2.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.38/2.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.38/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.38/2.55  --sup_full_triv                         [TrivRules;PropSubs]
% 15.38/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.38/2.55  --sup_full_bw                           [BwDemod]
% 15.38/2.55  --sup_immed_triv                        [TrivRules]
% 15.38/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.38/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.38/2.55  --sup_immed_bw_main                     []
% 15.38/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.38/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.38/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.38/2.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.38/2.55  
% 15.38/2.55  ------ Combination Options
% 15.38/2.55  
% 15.38/2.55  --comb_res_mult                         3
% 15.38/2.55  --comb_sup_mult                         2
% 15.38/2.55  --comb_inst_mult                        10
% 15.38/2.55  
% 15.38/2.55  ------ Debug Options
% 15.38/2.55  
% 15.38/2.55  --dbg_backtrace                         false
% 15.38/2.55  --dbg_dump_prop_clauses                 false
% 15.38/2.55  --dbg_dump_prop_clauses_file            -
% 15.38/2.55  --dbg_out_stat                          false
% 15.38/2.55  ------ Parsing...
% 15.38/2.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.38/2.55  
% 15.38/2.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.38/2.55  
% 15.38/2.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.38/2.55  
% 15.38/2.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.38/2.55  ------ Proving...
% 15.38/2.55  ------ Problem Properties 
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  clauses                                 18
% 15.38/2.55  conjectures                             1
% 15.38/2.55  EPR                                     2
% 15.38/2.55  Horn                                    15
% 15.38/2.55  unary                                   6
% 15.38/2.55  binary                                  7
% 15.38/2.55  lits                                    39
% 15.38/2.55  lits eq                                 10
% 15.38/2.55  fd_pure                                 0
% 15.38/2.55  fd_pseudo                               0
% 15.38/2.55  fd_cond                                 0
% 15.38/2.55  fd_pseudo_cond                          1
% 15.38/2.55  AC symbols                              0
% 15.38/2.55  
% 15.38/2.55  ------ Schedule dynamic 5 is on 
% 15.38/2.55  
% 15.38/2.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  ------ 
% 15.38/2.55  Current options:
% 15.38/2.55  ------ 
% 15.38/2.55  
% 15.38/2.55  ------ Input Options
% 15.38/2.55  
% 15.38/2.55  --out_options                           all
% 15.38/2.55  --tptp_safe_out                         true
% 15.38/2.55  --problem_path                          ""
% 15.38/2.55  --include_path                          ""
% 15.38/2.55  --clausifier                            res/vclausify_rel
% 15.38/2.55  --clausifier_options                    --mode clausify
% 15.38/2.55  --stdin                                 false
% 15.38/2.55  --stats_out                             all
% 15.38/2.55  
% 15.38/2.55  ------ General Options
% 15.38/2.55  
% 15.38/2.55  --fof                                   false
% 15.38/2.55  --time_out_real                         305.
% 15.38/2.55  --time_out_virtual                      -1.
% 15.38/2.55  --symbol_type_check                     false
% 15.38/2.55  --clausify_out                          false
% 15.38/2.55  --sig_cnt_out                           false
% 15.38/2.55  --trig_cnt_out                          false
% 15.38/2.55  --trig_cnt_out_tolerance                1.
% 15.38/2.55  --trig_cnt_out_sk_spl                   false
% 15.38/2.55  --abstr_cl_out                          false
% 15.38/2.55  
% 15.38/2.55  ------ Global Options
% 15.38/2.55  
% 15.38/2.55  --schedule                              default
% 15.38/2.55  --add_important_lit                     false
% 15.38/2.55  --prop_solver_per_cl                    1000
% 15.38/2.55  --min_unsat_core                        false
% 15.38/2.55  --soft_assumptions                      false
% 15.38/2.55  --soft_lemma_size                       3
% 15.38/2.55  --prop_impl_unit_size                   0
% 15.38/2.55  --prop_impl_unit                        []
% 15.38/2.55  --share_sel_clauses                     true
% 15.38/2.55  --reset_solvers                         false
% 15.38/2.55  --bc_imp_inh                            [conj_cone]
% 15.38/2.55  --conj_cone_tolerance                   3.
% 15.38/2.55  --extra_neg_conj                        none
% 15.38/2.55  --large_theory_mode                     true
% 15.38/2.55  --prolific_symb_bound                   200
% 15.38/2.55  --lt_threshold                          2000
% 15.38/2.55  --clause_weak_htbl                      true
% 15.38/2.55  --gc_record_bc_elim                     false
% 15.38/2.55  
% 15.38/2.55  ------ Preprocessing Options
% 15.38/2.55  
% 15.38/2.55  --preprocessing_flag                    true
% 15.38/2.55  --time_out_prep_mult                    0.1
% 15.38/2.55  --splitting_mode                        input
% 15.38/2.55  --splitting_grd                         true
% 15.38/2.55  --splitting_cvd                         false
% 15.38/2.55  --splitting_cvd_svl                     false
% 15.38/2.55  --splitting_nvd                         32
% 15.38/2.55  --sub_typing                            true
% 15.38/2.55  --prep_gs_sim                           true
% 15.38/2.55  --prep_unflatten                        true
% 15.38/2.55  --prep_res_sim                          true
% 15.38/2.55  --prep_upred                            true
% 15.38/2.55  --prep_sem_filter                       exhaustive
% 15.38/2.55  --prep_sem_filter_out                   false
% 15.38/2.55  --pred_elim                             true
% 15.38/2.55  --res_sim_input                         true
% 15.38/2.55  --eq_ax_congr_red                       true
% 15.38/2.55  --pure_diseq_elim                       true
% 15.38/2.55  --brand_transform                       false
% 15.38/2.55  --non_eq_to_eq                          false
% 15.38/2.55  --prep_def_merge                        true
% 15.38/2.55  --prep_def_merge_prop_impl              false
% 15.38/2.55  --prep_def_merge_mbd                    true
% 15.38/2.55  --prep_def_merge_tr_red                 false
% 15.38/2.55  --prep_def_merge_tr_cl                  false
% 15.38/2.55  --smt_preprocessing                     true
% 15.38/2.55  --smt_ac_axioms                         fast
% 15.38/2.55  --preprocessed_out                      false
% 15.38/2.55  --preprocessed_stats                    false
% 15.38/2.55  
% 15.38/2.55  ------ Abstraction refinement Options
% 15.38/2.55  
% 15.38/2.55  --abstr_ref                             []
% 15.38/2.55  --abstr_ref_prep                        false
% 15.38/2.55  --abstr_ref_until_sat                   false
% 15.38/2.55  --abstr_ref_sig_restrict                funpre
% 15.38/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.38/2.55  --abstr_ref_under                       []
% 15.38/2.55  
% 15.38/2.55  ------ SAT Options
% 15.38/2.55  
% 15.38/2.55  --sat_mode                              false
% 15.38/2.55  --sat_fm_restart_options                ""
% 15.38/2.55  --sat_gr_def                            false
% 15.38/2.55  --sat_epr_types                         true
% 15.38/2.55  --sat_non_cyclic_types                  false
% 15.38/2.55  --sat_finite_models                     false
% 15.38/2.55  --sat_fm_lemmas                         false
% 15.38/2.55  --sat_fm_prep                           false
% 15.38/2.55  --sat_fm_uc_incr                        true
% 15.38/2.55  --sat_out_model                         small
% 15.38/2.55  --sat_out_clauses                       false
% 15.38/2.55  
% 15.38/2.55  ------ QBF Options
% 15.38/2.55  
% 15.38/2.55  --qbf_mode                              false
% 15.38/2.55  --qbf_elim_univ                         false
% 15.38/2.55  --qbf_dom_inst                          none
% 15.38/2.55  --qbf_dom_pre_inst                      false
% 15.38/2.55  --qbf_sk_in                             false
% 15.38/2.55  --qbf_pred_elim                         true
% 15.38/2.55  --qbf_split                             512
% 15.38/2.55  
% 15.38/2.55  ------ BMC1 Options
% 15.38/2.55  
% 15.38/2.55  --bmc1_incremental                      false
% 15.38/2.55  --bmc1_axioms                           reachable_all
% 15.38/2.55  --bmc1_min_bound                        0
% 15.38/2.55  --bmc1_max_bound                        -1
% 15.38/2.55  --bmc1_max_bound_default                -1
% 15.38/2.55  --bmc1_symbol_reachability              true
% 15.38/2.55  --bmc1_property_lemmas                  false
% 15.38/2.55  --bmc1_k_induction                      false
% 15.38/2.55  --bmc1_non_equiv_states                 false
% 15.38/2.55  --bmc1_deadlock                         false
% 15.38/2.55  --bmc1_ucm                              false
% 15.38/2.55  --bmc1_add_unsat_core                   none
% 15.38/2.55  --bmc1_unsat_core_children              false
% 15.38/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.38/2.55  --bmc1_out_stat                         full
% 15.38/2.55  --bmc1_ground_init                      false
% 15.38/2.55  --bmc1_pre_inst_next_state              false
% 15.38/2.55  --bmc1_pre_inst_state                   false
% 15.38/2.55  --bmc1_pre_inst_reach_state             false
% 15.38/2.55  --bmc1_out_unsat_core                   false
% 15.38/2.55  --bmc1_aig_witness_out                  false
% 15.38/2.55  --bmc1_verbose                          false
% 15.38/2.55  --bmc1_dump_clauses_tptp                false
% 15.38/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.38/2.55  --bmc1_dump_file                        -
% 15.38/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.38/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.38/2.55  --bmc1_ucm_extend_mode                  1
% 15.38/2.55  --bmc1_ucm_init_mode                    2
% 15.38/2.55  --bmc1_ucm_cone_mode                    none
% 15.38/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.38/2.55  --bmc1_ucm_relax_model                  4
% 15.38/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.38/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.38/2.55  --bmc1_ucm_layered_model                none
% 15.38/2.55  --bmc1_ucm_max_lemma_size               10
% 15.38/2.55  
% 15.38/2.55  ------ AIG Options
% 15.38/2.55  
% 15.38/2.55  --aig_mode                              false
% 15.38/2.55  
% 15.38/2.55  ------ Instantiation Options
% 15.38/2.55  
% 15.38/2.55  --instantiation_flag                    true
% 15.38/2.55  --inst_sos_flag                         false
% 15.38/2.55  --inst_sos_phase                        true
% 15.38/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.38/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.38/2.55  --inst_lit_sel_side                     none
% 15.38/2.55  --inst_solver_per_active                1400
% 15.38/2.55  --inst_solver_calls_frac                1.
% 15.38/2.55  --inst_passive_queue_type               priority_queues
% 15.38/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.38/2.55  --inst_passive_queues_freq              [25;2]
% 15.38/2.55  --inst_dismatching                      true
% 15.38/2.55  --inst_eager_unprocessed_to_passive     true
% 15.38/2.55  --inst_prop_sim_given                   true
% 15.38/2.55  --inst_prop_sim_new                     false
% 15.38/2.55  --inst_subs_new                         false
% 15.38/2.55  --inst_eq_res_simp                      false
% 15.38/2.55  --inst_subs_given                       false
% 15.38/2.55  --inst_orphan_elimination               true
% 15.38/2.55  --inst_learning_loop_flag               true
% 15.38/2.55  --inst_learning_start                   3000
% 15.38/2.55  --inst_learning_factor                  2
% 15.38/2.55  --inst_start_prop_sim_after_learn       3
% 15.38/2.55  --inst_sel_renew                        solver
% 15.38/2.55  --inst_lit_activity_flag                true
% 15.38/2.55  --inst_restr_to_given                   false
% 15.38/2.55  --inst_activity_threshold               500
% 15.38/2.55  --inst_out_proof                        true
% 15.38/2.55  
% 15.38/2.55  ------ Resolution Options
% 15.38/2.55  
% 15.38/2.55  --resolution_flag                       false
% 15.38/2.55  --res_lit_sel                           adaptive
% 15.38/2.55  --res_lit_sel_side                      none
% 15.38/2.55  --res_ordering                          kbo
% 15.38/2.55  --res_to_prop_solver                    active
% 15.38/2.55  --res_prop_simpl_new                    false
% 15.38/2.55  --res_prop_simpl_given                  true
% 15.38/2.55  --res_passive_queue_type                priority_queues
% 15.38/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.38/2.55  --res_passive_queues_freq               [15;5]
% 15.38/2.55  --res_forward_subs                      full
% 15.38/2.55  --res_backward_subs                     full
% 15.38/2.55  --res_forward_subs_resolution           true
% 15.38/2.55  --res_backward_subs_resolution          true
% 15.38/2.55  --res_orphan_elimination                true
% 15.38/2.55  --res_time_limit                        2.
% 15.38/2.55  --res_out_proof                         true
% 15.38/2.55  
% 15.38/2.55  ------ Superposition Options
% 15.38/2.55  
% 15.38/2.55  --superposition_flag                    true
% 15.38/2.55  --sup_passive_queue_type                priority_queues
% 15.38/2.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.38/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.38/2.55  --demod_completeness_check              fast
% 15.38/2.55  --demod_use_ground                      true
% 15.38/2.55  --sup_to_prop_solver                    passive
% 15.38/2.55  --sup_prop_simpl_new                    true
% 15.38/2.55  --sup_prop_simpl_given                  true
% 15.38/2.55  --sup_fun_splitting                     false
% 15.38/2.55  --sup_smt_interval                      50000
% 15.38/2.55  
% 15.38/2.55  ------ Superposition Simplification Setup
% 15.38/2.55  
% 15.38/2.55  --sup_indices_passive                   []
% 15.38/2.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.38/2.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.38/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.38/2.55  --sup_full_triv                         [TrivRules;PropSubs]
% 15.38/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.38/2.55  --sup_full_bw                           [BwDemod]
% 15.38/2.55  --sup_immed_triv                        [TrivRules]
% 15.38/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.38/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.38/2.55  --sup_immed_bw_main                     []
% 15.38/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.38/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.38/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.38/2.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.38/2.55  
% 15.38/2.55  ------ Combination Options
% 15.38/2.55  
% 15.38/2.55  --comb_res_mult                         3
% 15.38/2.55  --comb_sup_mult                         2
% 15.38/2.55  --comb_inst_mult                        10
% 15.38/2.55  
% 15.38/2.55  ------ Debug Options
% 15.38/2.55  
% 15.38/2.55  --dbg_backtrace                         false
% 15.38/2.55  --dbg_dump_prop_clauses                 false
% 15.38/2.55  --dbg_dump_prop_clauses_file            -
% 15.38/2.55  --dbg_out_stat                          false
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  ------ Proving...
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  % SZS status Theorem for theBenchmark.p
% 15.38/2.55  
% 15.38/2.55  % SZS output start CNFRefutation for theBenchmark.p
% 15.38/2.55  
% 15.38/2.55  fof(f6,axiom,(
% 15.38/2.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f16,plain,(
% 15.38/2.55    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 15.38/2.55    inference(ennf_transformation,[],[f6])).
% 15.38/2.55  
% 15.38/2.55  fof(f39,plain,(
% 15.38/2.55    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f16])).
% 15.38/2.55  
% 15.38/2.55  fof(f7,axiom,(
% 15.38/2.55    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f17,plain,(
% 15.38/2.55    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 15.38/2.55    inference(ennf_transformation,[],[f7])).
% 15.38/2.55  
% 15.38/2.55  fof(f40,plain,(
% 15.38/2.55    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f17])).
% 15.38/2.55  
% 15.38/2.55  fof(f10,axiom,(
% 15.38/2.55    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f49,plain,(
% 15.38/2.55    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 15.38/2.55    inference(cnf_transformation,[],[f10])).
% 15.38/2.55  
% 15.38/2.55  fof(f9,axiom,(
% 15.38/2.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f19,plain,(
% 15.38/2.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 15.38/2.55    inference(ennf_transformation,[],[f9])).
% 15.38/2.55  
% 15.38/2.55  fof(f20,plain,(
% 15.38/2.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 15.38/2.55    inference(flattening,[],[f19])).
% 15.38/2.55  
% 15.38/2.55  fof(f24,plain,(
% 15.38/2.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.38/2.55    inference(nnf_transformation,[],[f20])).
% 15.38/2.55  
% 15.38/2.55  fof(f25,plain,(
% 15.38/2.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.38/2.55    inference(flattening,[],[f24])).
% 15.38/2.55  
% 15.38/2.55  fof(f26,plain,(
% 15.38/2.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.38/2.55    inference(rectify,[],[f25])).
% 15.38/2.55  
% 15.38/2.55  fof(f27,plain,(
% 15.38/2.55    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 15.38/2.55    introduced(choice_axiom,[])).
% 15.38/2.55  
% 15.38/2.55  fof(f28,plain,(
% 15.38/2.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.38/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 15.38/2.55  
% 15.38/2.55  fof(f42,plain,(
% 15.38/2.55    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f28])).
% 15.38/2.55  
% 15.38/2.55  fof(f59,plain,(
% 15.38/2.55    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 15.38/2.55    inference(equality_resolution,[],[f42])).
% 15.38/2.55  
% 15.38/2.55  fof(f5,axiom,(
% 15.38/2.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f37,plain,(
% 15.38/2.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.38/2.55    inference(cnf_transformation,[],[f5])).
% 15.38/2.55  
% 15.38/2.55  fof(f4,axiom,(
% 15.38/2.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f15,plain,(
% 15.38/2.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.38/2.55    inference(ennf_transformation,[],[f4])).
% 15.38/2.55  
% 15.38/2.55  fof(f36,plain,(
% 15.38/2.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f15])).
% 15.38/2.55  
% 15.38/2.55  fof(f38,plain,(
% 15.38/2.55    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f16])).
% 15.38/2.55  
% 15.38/2.55  fof(f8,axiom,(
% 15.38/2.55    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f18,plain,(
% 15.38/2.55    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.38/2.55    inference(ennf_transformation,[],[f8])).
% 15.38/2.55  
% 15.38/2.55  fof(f41,plain,(
% 15.38/2.55    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f18])).
% 15.38/2.55  
% 15.38/2.55  fof(f3,axiom,(
% 15.38/2.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f14,plain,(
% 15.38/2.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 15.38/2.55    inference(ennf_transformation,[],[f3])).
% 15.38/2.55  
% 15.38/2.55  fof(f35,plain,(
% 15.38/2.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f14])).
% 15.38/2.55  
% 15.38/2.55  fof(f1,axiom,(
% 15.38/2.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f22,plain,(
% 15.38/2.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.38/2.55    inference(nnf_transformation,[],[f1])).
% 15.38/2.55  
% 15.38/2.55  fof(f23,plain,(
% 15.38/2.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.38/2.55    inference(flattening,[],[f22])).
% 15.38/2.55  
% 15.38/2.55  fof(f32,plain,(
% 15.38/2.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.38/2.55    inference(cnf_transformation,[],[f23])).
% 15.38/2.55  
% 15.38/2.55  fof(f51,plain,(
% 15.38/2.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.38/2.55    inference(equality_resolution,[],[f32])).
% 15.38/2.55  
% 15.38/2.55  fof(f2,axiom,(
% 15.38/2.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f13,plain,(
% 15.38/2.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.38/2.55    inference(ennf_transformation,[],[f2])).
% 15.38/2.55  
% 15.38/2.55  fof(f34,plain,(
% 15.38/2.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.38/2.55    inference(cnf_transformation,[],[f13])).
% 15.38/2.55  
% 15.38/2.55  fof(f11,conjecture,(
% 15.38/2.55    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 15.38/2.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.38/2.55  
% 15.38/2.55  fof(f12,negated_conjecture,(
% 15.38/2.55    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 15.38/2.55    inference(negated_conjecture,[],[f11])).
% 15.38/2.55  
% 15.38/2.55  fof(f21,plain,(
% 15.38/2.55    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 15.38/2.55    inference(ennf_transformation,[],[f12])).
% 15.38/2.55  
% 15.38/2.55  fof(f29,plain,(
% 15.38/2.55    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 15.38/2.55    introduced(choice_axiom,[])).
% 15.38/2.55  
% 15.38/2.55  fof(f30,plain,(
% 15.38/2.55    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 15.38/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f29])).
% 15.38/2.55  
% 15.38/2.55  fof(f50,plain,(
% 15.38/2.55    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 15.38/2.55    inference(cnf_transformation,[],[f30])).
% 15.38/2.55  
% 15.38/2.55  cnf(c_7,plain,
% 15.38/2.55      ( ~ r1_tarski(X0,X1)
% 15.38/2.55      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 15.38/2.55      inference(cnf_transformation,[],[f39]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_780,plain,
% 15.38/2.55      ( r1_tarski(X0,X1) != iProver_top
% 15.38/2.55      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_9,plain,
% 15.38/2.55      ( ~ v1_relat_1(X0)
% 15.38/2.55      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 15.38/2.55      inference(cnf_transformation,[],[f40]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_18,plain,
% 15.38/2.55      ( v1_relat_1(k1_wellord2(X0)) ),
% 15.38/2.55      inference(cnf_transformation,[],[f49]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_290,plain,
% 15.38/2.55      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 15.38/2.55      | k1_wellord2(X1) != X0 ),
% 15.38/2.55      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_291,plain,
% 15.38/2.55      ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = k3_relat_1(k1_wellord2(X0)) ),
% 15.38/2.55      inference(unflattening,[status(thm)],[c_290]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_17,plain,
% 15.38/2.55      ( ~ v1_relat_1(k1_wellord2(X0))
% 15.38/2.55      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 15.38/2.55      inference(cnf_transformation,[],[f59]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_115,plain,
% 15.38/2.55      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 15.38/2.55      inference(global_propositional_subsumption,
% 15.38/2.55                [status(thm)],
% 15.38/2.55                [c_17,c_18]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_795,plain,
% 15.38/2.55      ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
% 15.38/2.55      inference(light_normalisation,[status(thm)],[c_291,c_115]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_6,plain,
% 15.38/2.55      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.38/2.55      inference(cnf_transformation,[],[f37]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_781,plain,
% 15.38/2.55      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_904,plain,
% 15.38/2.55      ( r1_tarski(k1_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_795,c_781]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_5,plain,
% 15.38/2.55      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.38/2.55      inference(cnf_transformation,[],[f36]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_782,plain,
% 15.38/2.55      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_977,plain,
% 15.38/2.55      ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X0) = X0 ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_904,c_782]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_8,plain,
% 15.38/2.55      ( ~ r1_tarski(X0,X1)
% 15.38/2.55      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 15.38/2.55      inference(cnf_transformation,[],[f38]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_779,plain,
% 15.38/2.55      ( r1_tarski(X0,X1) != iProver_top
% 15.38/2.55      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_1241,plain,
% 15.38/2.55      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,X1)
% 15.38/2.55      | r1_tarski(X0,X2) != iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_779,c_782]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_7946,plain,
% 15.38/2.55      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_781,c_1241]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_10899,plain,
% 15.38/2.55      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),X1)) = iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_7946,c_781]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_11117,plain,
% 15.38/2.55      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_977,c_10899]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_10,plain,
% 15.38/2.55      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 15.38/2.55      | ~ v1_relat_1(X0) ),
% 15.38/2.55      inference(cnf_transformation,[],[f41]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_281,plain,
% 15.38/2.55      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 15.38/2.55      | k1_wellord2(X1) != X0 ),
% 15.38/2.55      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_282,plain,
% 15.38/2.55      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) ),
% 15.38/2.55      inference(unflattening,[status(thm)],[c_281]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_773,plain,
% 15.38/2.55      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_976,plain,
% 15.38/2.55      ( k2_xboole_0(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_773,c_782]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_4,plain,
% 15.38/2.55      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 15.38/2.55      inference(cnf_transformation,[],[f35]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_783,plain,
% 15.38/2.55      ( r1_tarski(X0,X1) = iProver_top
% 15.38/2.55      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_3046,plain,
% 15.38/2.55      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))),X1) != iProver_top
% 15.38/2.55      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_976,c_783]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_67014,plain,
% 15.38/2.55      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0)))) = iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_11117,c_3046]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_67529,plain,
% 15.38/2.55      ( k2_xboole_0(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0)))) = k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0))) ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_67014,c_782]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_72814,plain,
% 15.38/2.55      ( r1_tarski(k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0))),X1) != iProver_top
% 15.38/2.55      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_67529,c_783]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_74639,plain,
% 15.38/2.55      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X1)) = iProver_top
% 15.38/2.55      | r1_tarski(k2_relat_1(k1_wellord2(X0)),X1) != iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_780,c_72814]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_74731,plain,
% 15.38/2.55      ( r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) = iProver_top
% 15.38/2.55      | r1_tarski(k2_relat_1(k1_wellord2(sK2)),sK2) != iProver_top ),
% 15.38/2.55      inference(instantiation,[status(thm)],[c_74639]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_1,plain,
% 15.38/2.55      ( r1_tarski(X0,X0) ),
% 15.38/2.55      inference(cnf_transformation,[],[f51]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_785,plain,
% 15.38/2.55      ( r1_tarski(X0,X0) = iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_3,plain,
% 15.38/2.55      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 15.38/2.55      inference(cnf_transformation,[],[f34]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_784,plain,
% 15.38/2.55      ( r1_tarski(X0,X1) != iProver_top
% 15.38/2.55      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_1220,plain,
% 15.38/2.55      ( r1_tarski(X0,X1) = iProver_top
% 15.38/2.55      | r1_tarski(X0,k2_relat_1(k1_wellord2(X1))) != iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_795,c_784]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_3262,plain,
% 15.38/2.55      ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
% 15.38/2.55      inference(superposition,[status(thm)],[c_785,c_1220]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_3280,plain,
% 15.38/2.55      ( r1_tarski(k2_relat_1(k1_wellord2(sK2)),sK2) = iProver_top ),
% 15.38/2.55      inference(instantiation,[status(thm)],[c_3262]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_19,negated_conjecture,
% 15.38/2.55      ( ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
% 15.38/2.55      inference(cnf_transformation,[],[f50]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(c_20,plain,
% 15.38/2.55      ( r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) != iProver_top ),
% 15.38/2.55      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.38/2.55  
% 15.38/2.55  cnf(contradiction,plain,
% 15.38/2.55      ( $false ),
% 15.38/2.55      inference(minisat,[status(thm)],[c_74731,c_3280,c_20]) ).
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  % SZS output end CNFRefutation for theBenchmark.p
% 15.38/2.55  
% 15.38/2.55  ------                               Statistics
% 15.38/2.55  
% 15.38/2.55  ------ General
% 15.38/2.55  
% 15.38/2.55  abstr_ref_over_cycles:                  0
% 15.38/2.55  abstr_ref_under_cycles:                 0
% 15.38/2.55  gc_basic_clause_elim:                   0
% 15.38/2.55  forced_gc_time:                         0
% 15.38/2.55  parsing_time:                           0.013
% 15.38/2.55  unif_index_cands_time:                  0.
% 15.38/2.55  unif_index_add_time:                    0.
% 15.38/2.55  orderings_time:                         0.
% 15.38/2.55  out_proof_time:                         0.009
% 15.38/2.55  total_time:                             1.794
% 15.38/2.55  num_of_symbols:                         44
% 15.38/2.55  num_of_terms:                           74106
% 15.38/2.55  
% 15.38/2.55  ------ Preprocessing
% 15.38/2.55  
% 15.38/2.55  num_of_splits:                          0
% 15.38/2.55  num_of_split_atoms:                     0
% 15.38/2.55  num_of_reused_defs:                     0
% 15.38/2.55  num_eq_ax_congr_red:                    4
% 15.38/2.55  num_of_sem_filtered_clauses:            1
% 15.38/2.55  num_of_subtypes:                        0
% 15.38/2.55  monotx_restored_types:                  0
% 15.38/2.55  sat_num_of_epr_types:                   0
% 15.38/2.55  sat_num_of_non_cyclic_types:            0
% 15.38/2.55  sat_guarded_non_collapsed_types:        0
% 15.38/2.55  num_pure_diseq_elim:                    0
% 15.38/2.55  simp_replaced_by:                       0
% 15.38/2.55  res_preprocessed:                       100
% 15.38/2.55  prep_upred:                             0
% 15.38/2.55  prep_unflattend:                        6
% 15.38/2.55  smt_new_axioms:                         0
% 15.38/2.55  pred_elim_cands:                        2
% 15.38/2.55  pred_elim:                              1
% 15.38/2.55  pred_elim_cl:                           1
% 15.38/2.55  pred_elim_cycles:                       3
% 15.38/2.55  merged_defs:                            0
% 15.38/2.55  merged_defs_ncl:                        0
% 15.38/2.55  bin_hyper_res:                          0
% 15.38/2.55  prep_cycles:                            4
% 15.38/2.55  pred_elim_time:                         0.005
% 15.38/2.55  splitting_time:                         0.
% 15.38/2.55  sem_filter_time:                        0.
% 15.38/2.55  monotx_time:                            0.
% 15.38/2.55  subtype_inf_time:                       0.
% 15.38/2.55  
% 15.38/2.55  ------ Problem properties
% 15.38/2.55  
% 15.38/2.55  clauses:                                18
% 15.38/2.55  conjectures:                            1
% 15.38/2.55  epr:                                    2
% 15.38/2.55  horn:                                   15
% 15.38/2.55  ground:                                 1
% 15.38/2.55  unary:                                  6
% 15.38/2.55  binary:                                 7
% 15.38/2.55  lits:                                   39
% 15.38/2.55  lits_eq:                                10
% 15.38/2.55  fd_pure:                                0
% 15.38/2.55  fd_pseudo:                              0
% 15.38/2.55  fd_cond:                                0
% 15.38/2.55  fd_pseudo_cond:                         1
% 15.38/2.55  ac_symbols:                             0
% 15.38/2.55  
% 15.38/2.55  ------ Propositional Solver
% 15.38/2.55  
% 15.38/2.55  prop_solver_calls:                      34
% 15.38/2.55  prop_fast_solver_calls:                 857
% 15.38/2.55  smt_solver_calls:                       0
% 15.38/2.55  smt_fast_solver_calls:                  0
% 15.38/2.55  prop_num_of_clauses:                    24511
% 15.38/2.55  prop_preprocess_simplified:             28086
% 15.38/2.55  prop_fo_subsumed:                       1
% 15.38/2.55  prop_solver_time:                       0.
% 15.38/2.55  smt_solver_time:                        0.
% 15.38/2.55  smt_fast_solver_time:                   0.
% 15.38/2.55  prop_fast_solver_time:                  0.
% 15.38/2.55  prop_unsat_core_time:                   0.002
% 15.38/2.55  
% 15.38/2.55  ------ QBF
% 15.38/2.55  
% 15.38/2.55  qbf_q_res:                              0
% 15.38/2.55  qbf_num_tautologies:                    0
% 15.38/2.55  qbf_prep_cycles:                        0
% 15.38/2.55  
% 15.38/2.55  ------ BMC1
% 15.38/2.55  
% 15.38/2.55  bmc1_current_bound:                     -1
% 15.38/2.55  bmc1_last_solved_bound:                 -1
% 15.38/2.55  bmc1_unsat_core_size:                   -1
% 15.38/2.55  bmc1_unsat_core_parents_size:           -1
% 15.38/2.55  bmc1_merge_next_fun:                    0
% 15.38/2.55  bmc1_unsat_core_clauses_time:           0.
% 15.38/2.55  
% 15.38/2.55  ------ Instantiation
% 15.38/2.55  
% 15.38/2.55  inst_num_of_clauses:                    4542
% 15.38/2.55  inst_num_in_passive:                    1195
% 15.38/2.55  inst_num_in_active:                     1088
% 15.38/2.55  inst_num_in_unprocessed:                2260
% 15.38/2.55  inst_num_of_loops:                      1360
% 15.38/2.55  inst_num_of_learning_restarts:          0
% 15.38/2.55  inst_num_moves_active_passive:          267
% 15.38/2.55  inst_lit_activity:                      0
% 15.38/2.55  inst_lit_activity_moves:                1
% 15.38/2.55  inst_num_tautologies:                   0
% 15.38/2.55  inst_num_prop_implied:                  0
% 15.38/2.55  inst_num_existing_simplified:           0
% 15.38/2.55  inst_num_eq_res_simplified:             0
% 15.38/2.55  inst_num_child_elim:                    0
% 15.38/2.55  inst_num_of_dismatching_blockings:      3373
% 15.38/2.55  inst_num_of_non_proper_insts:           4653
% 15.38/2.55  inst_num_of_duplicates:                 0
% 15.38/2.55  inst_inst_num_from_inst_to_res:         0
% 15.38/2.55  inst_dismatching_checking_time:         0.
% 15.38/2.55  
% 15.38/2.55  ------ Resolution
% 15.38/2.55  
% 15.38/2.55  res_num_of_clauses:                     0
% 15.38/2.55  res_num_in_passive:                     0
% 15.38/2.55  res_num_in_active:                      0
% 15.38/2.55  res_num_of_loops:                       104
% 15.38/2.55  res_forward_subset_subsumed:            1123
% 15.38/2.55  res_backward_subset_subsumed:           4
% 15.38/2.55  res_forward_subsumed:                   0
% 15.38/2.55  res_backward_subsumed:                  0
% 15.38/2.55  res_forward_subsumption_resolution:     0
% 15.38/2.55  res_backward_subsumption_resolution:    0
% 15.38/2.55  res_clause_to_clause_subsumption:       78615
% 15.38/2.55  res_orphan_elimination:                 0
% 15.38/2.55  res_tautology_del:                      258
% 15.38/2.55  res_num_eq_res_simplified:              0
% 15.38/2.55  res_num_sel_changes:                    0
% 15.38/2.55  res_moves_from_active_to_pass:          0
% 15.38/2.55  
% 15.38/2.55  ------ Superposition
% 15.38/2.55  
% 15.38/2.55  sup_time_total:                         0.
% 15.38/2.55  sup_time_generating:                    0.
% 15.38/2.55  sup_time_sim_full:                      0.
% 15.38/2.55  sup_time_sim_immed:                     0.
% 15.38/2.55  
% 15.38/2.55  sup_num_of_clauses:                     4919
% 15.38/2.55  sup_num_in_active:                      272
% 15.38/2.55  sup_num_in_passive:                     4647
% 15.38/2.55  sup_num_of_loops:                       271
% 15.38/2.55  sup_fw_superposition:                   8248
% 15.38/2.55  sup_bw_superposition:                   7152
% 15.38/2.55  sup_immediate_simplified:               4274
% 15.38/2.55  sup_given_eliminated:                   0
% 15.38/2.55  comparisons_done:                       0
% 15.38/2.55  comparisons_avoided:                    0
% 15.38/2.55  
% 15.38/2.55  ------ Simplifications
% 15.38/2.55  
% 15.38/2.55  
% 15.38/2.55  sim_fw_subset_subsumed:                 66
% 15.38/2.55  sim_bw_subset_subsumed:                 0
% 15.38/2.55  sim_fw_subsumed:                        1236
% 15.38/2.55  sim_bw_subsumed:                        11
% 15.38/2.55  sim_fw_subsumption_res:                 0
% 15.38/2.55  sim_bw_subsumption_res:                 0
% 15.38/2.55  sim_tautology_del:                      131
% 15.38/2.55  sim_eq_tautology_del:                   335
% 15.38/2.55  sim_eq_res_simp:                        0
% 15.38/2.55  sim_fw_demodulated:                     1236
% 15.38/2.55  sim_bw_demodulated:                     0
% 15.38/2.55  sim_light_normalised:                   1985
% 15.38/2.55  sim_joinable_taut:                      0
% 15.38/2.55  sim_joinable_simp:                      0
% 15.38/2.55  sim_ac_normalised:                      0
% 15.38/2.55  sim_smt_subsumption:                    0
% 15.38/2.55  
%------------------------------------------------------------------------------
