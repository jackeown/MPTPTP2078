%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:52 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 154 expanded)
%              Number of clauses        :   52 (  69 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   18
%              Number of atoms          :  262 ( 459 expanded)
%              Number of equality atoms :   93 ( 153 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f23])).

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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f11,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).

fof(f49,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_807,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_wellord2(sK2),X0),k2_zfmisc_1(sK2,sK2))
    | r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_19457,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))),k2_zfmisc_1(sK2,sK2))
    | r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_719,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_272,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | k1_wellord2(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_273,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = k3_relat_1(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_17,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_109,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_729,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_273,c_109])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_718,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1966,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_relat_1(k1_wellord2(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_718])).

cnf(c_7434,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_1966])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_716,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7609,plain,
    ( k2_xboole_0(k2_relat_1(k1_wellord2(X0)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_7434,c_716])).

cnf(c_8,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_715,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1019,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_715])).

cnf(c_1146,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_1019])).

cnf(c_1558,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_1146,c_716])).

cnf(c_7,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_717,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1770,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_717])).

cnf(c_2317,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_xboole_0(k2_zfmisc_1(X0,k2_xboole_0(X1,X2)),X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1770])).

cnf(c_3125,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,k2_xboole_0(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_2317])).

cnf(c_8527,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X1))),k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7609,c_3125])).

cnf(c_8662,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X1))),k2_zfmisc_1(X0,X1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8527])).

cnf(c_8664,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))),k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_8662])).

cnf(c_451,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_846,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(k1_wellord2(sK2),X2),k2_zfmisc_1(sK2,sK2))
    | k2_zfmisc_1(sK2,sK2) != X1
    | k2_xboole_0(k1_wellord2(sK2),X2) != X0 ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_1056,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(k2_xboole_0(k1_wellord2(sK2),X3),k2_zfmisc_1(sK2,sK2))
    | k2_zfmisc_1(sK2,sK2) != k2_zfmisc_1(X1,X2)
    | k2_xboole_0(k1_wellord2(sK2),X3) != X0 ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_3856,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))),k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))),k2_zfmisc_1(sK2,sK2))
    | k2_zfmisc_1(sK2,sK2) != k2_zfmisc_1(X0,X1)
    | k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_3858,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))),k2_zfmisc_1(sK2,sK2))
    | r1_tarski(k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))),k2_zfmisc_1(sK2,sK2))
    | k2_zfmisc_1(sK2,sK2) != k2_zfmisc_1(sK2,sK2)
    | k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))) ),
    inference(instantiation,[status(thm)],[c_3856])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_263,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | k1_wellord2(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_264,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_709,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_902,plain,
    ( k2_xboole_0(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
    inference(superposition,[status(thm)],[c_709,c_716])).

cnf(c_914,plain,
    ( k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))) = k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_453,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_464,plain,
    ( k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_68,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_64,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19457,c_8664,c_3858,c_914,c_464,c_68,c_64,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.25/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/1.51  
% 7.25/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.25/1.51  
% 7.25/1.51  ------  iProver source info
% 7.25/1.51  
% 7.25/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.25/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.25/1.51  git: non_committed_changes: false
% 7.25/1.51  git: last_make_outside_of_git: false
% 7.25/1.51  
% 7.25/1.51  ------ 
% 7.25/1.51  
% 7.25/1.51  ------ Input Options
% 7.25/1.51  
% 7.25/1.51  --out_options                           all
% 7.25/1.51  --tptp_safe_out                         true
% 7.25/1.51  --problem_path                          ""
% 7.25/1.51  --include_path                          ""
% 7.25/1.51  --clausifier                            res/vclausify_rel
% 7.25/1.51  --clausifier_options                    --mode clausify
% 7.25/1.51  --stdin                                 false
% 7.25/1.51  --stats_out                             all
% 7.25/1.51  
% 7.25/1.51  ------ General Options
% 7.25/1.51  
% 7.25/1.51  --fof                                   false
% 7.25/1.51  --time_out_real                         305.
% 7.25/1.51  --time_out_virtual                      -1.
% 7.25/1.51  --symbol_type_check                     false
% 7.25/1.51  --clausify_out                          false
% 7.25/1.51  --sig_cnt_out                           false
% 7.25/1.51  --trig_cnt_out                          false
% 7.25/1.51  --trig_cnt_out_tolerance                1.
% 7.25/1.51  --trig_cnt_out_sk_spl                   false
% 7.25/1.51  --abstr_cl_out                          false
% 7.25/1.51  
% 7.25/1.51  ------ Global Options
% 7.25/1.51  
% 7.25/1.51  --schedule                              default
% 7.25/1.51  --add_important_lit                     false
% 7.25/1.51  --prop_solver_per_cl                    1000
% 7.25/1.51  --min_unsat_core                        false
% 7.25/1.51  --soft_assumptions                      false
% 7.25/1.51  --soft_lemma_size                       3
% 7.25/1.51  --prop_impl_unit_size                   0
% 7.25/1.51  --prop_impl_unit                        []
% 7.25/1.51  --share_sel_clauses                     true
% 7.25/1.51  --reset_solvers                         false
% 7.25/1.51  --bc_imp_inh                            [conj_cone]
% 7.25/1.51  --conj_cone_tolerance                   3.
% 7.25/1.51  --extra_neg_conj                        none
% 7.25/1.51  --large_theory_mode                     true
% 7.25/1.51  --prolific_symb_bound                   200
% 7.25/1.51  --lt_threshold                          2000
% 7.25/1.51  --clause_weak_htbl                      true
% 7.25/1.51  --gc_record_bc_elim                     false
% 7.25/1.51  
% 7.25/1.51  ------ Preprocessing Options
% 7.25/1.51  
% 7.25/1.51  --preprocessing_flag                    true
% 7.25/1.51  --time_out_prep_mult                    0.1
% 7.25/1.51  --splitting_mode                        input
% 7.25/1.51  --splitting_grd                         true
% 7.25/1.51  --splitting_cvd                         false
% 7.25/1.51  --splitting_cvd_svl                     false
% 7.25/1.51  --splitting_nvd                         32
% 7.25/1.51  --sub_typing                            true
% 7.25/1.51  --prep_gs_sim                           true
% 7.25/1.51  --prep_unflatten                        true
% 7.25/1.51  --prep_res_sim                          true
% 7.25/1.51  --prep_upred                            true
% 7.25/1.51  --prep_sem_filter                       exhaustive
% 7.25/1.51  --prep_sem_filter_out                   false
% 7.25/1.51  --pred_elim                             true
% 7.25/1.51  --res_sim_input                         true
% 7.25/1.51  --eq_ax_congr_red                       true
% 7.25/1.51  --pure_diseq_elim                       true
% 7.25/1.51  --brand_transform                       false
% 7.25/1.51  --non_eq_to_eq                          false
% 7.25/1.51  --prep_def_merge                        true
% 7.25/1.51  --prep_def_merge_prop_impl              false
% 7.25/1.51  --prep_def_merge_mbd                    true
% 7.25/1.51  --prep_def_merge_tr_red                 false
% 7.25/1.51  --prep_def_merge_tr_cl                  false
% 7.25/1.51  --smt_preprocessing                     true
% 7.25/1.51  --smt_ac_axioms                         fast
% 7.25/1.51  --preprocessed_out                      false
% 7.25/1.51  --preprocessed_stats                    false
% 7.25/1.51  
% 7.25/1.51  ------ Abstraction refinement Options
% 7.25/1.51  
% 7.25/1.51  --abstr_ref                             []
% 7.25/1.51  --abstr_ref_prep                        false
% 7.25/1.51  --abstr_ref_until_sat                   false
% 7.25/1.51  --abstr_ref_sig_restrict                funpre
% 7.25/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.51  --abstr_ref_under                       []
% 7.25/1.51  
% 7.25/1.51  ------ SAT Options
% 7.25/1.51  
% 7.25/1.51  --sat_mode                              false
% 7.25/1.51  --sat_fm_restart_options                ""
% 7.25/1.51  --sat_gr_def                            false
% 7.25/1.51  --sat_epr_types                         true
% 7.25/1.51  --sat_non_cyclic_types                  false
% 7.25/1.51  --sat_finite_models                     false
% 7.25/1.51  --sat_fm_lemmas                         false
% 7.25/1.51  --sat_fm_prep                           false
% 7.25/1.51  --sat_fm_uc_incr                        true
% 7.25/1.51  --sat_out_model                         small
% 7.25/1.51  --sat_out_clauses                       false
% 7.25/1.51  
% 7.25/1.51  ------ QBF Options
% 7.25/1.51  
% 7.25/1.51  --qbf_mode                              false
% 7.25/1.51  --qbf_elim_univ                         false
% 7.25/1.51  --qbf_dom_inst                          none
% 7.25/1.51  --qbf_dom_pre_inst                      false
% 7.25/1.51  --qbf_sk_in                             false
% 7.25/1.51  --qbf_pred_elim                         true
% 7.25/1.51  --qbf_split                             512
% 7.25/1.51  
% 7.25/1.51  ------ BMC1 Options
% 7.25/1.51  
% 7.25/1.51  --bmc1_incremental                      false
% 7.25/1.51  --bmc1_axioms                           reachable_all
% 7.25/1.51  --bmc1_min_bound                        0
% 7.25/1.51  --bmc1_max_bound                        -1
% 7.25/1.51  --bmc1_max_bound_default                -1
% 7.25/1.51  --bmc1_symbol_reachability              true
% 7.25/1.51  --bmc1_property_lemmas                  false
% 7.25/1.51  --bmc1_k_induction                      false
% 7.25/1.51  --bmc1_non_equiv_states                 false
% 7.25/1.51  --bmc1_deadlock                         false
% 7.25/1.51  --bmc1_ucm                              false
% 7.25/1.51  --bmc1_add_unsat_core                   none
% 7.25/1.51  --bmc1_unsat_core_children              false
% 7.25/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.51  --bmc1_out_stat                         full
% 7.25/1.51  --bmc1_ground_init                      false
% 7.25/1.51  --bmc1_pre_inst_next_state              false
% 7.25/1.51  --bmc1_pre_inst_state                   false
% 7.25/1.51  --bmc1_pre_inst_reach_state             false
% 7.25/1.51  --bmc1_out_unsat_core                   false
% 7.25/1.51  --bmc1_aig_witness_out                  false
% 7.25/1.51  --bmc1_verbose                          false
% 7.25/1.51  --bmc1_dump_clauses_tptp                false
% 7.25/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.51  --bmc1_dump_file                        -
% 7.25/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.51  --bmc1_ucm_extend_mode                  1
% 7.25/1.51  --bmc1_ucm_init_mode                    2
% 7.25/1.51  --bmc1_ucm_cone_mode                    none
% 7.25/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.51  --bmc1_ucm_relax_model                  4
% 7.25/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.51  --bmc1_ucm_layered_model                none
% 7.25/1.51  --bmc1_ucm_max_lemma_size               10
% 7.25/1.51  
% 7.25/1.51  ------ AIG Options
% 7.25/1.51  
% 7.25/1.51  --aig_mode                              false
% 7.25/1.51  
% 7.25/1.51  ------ Instantiation Options
% 7.25/1.51  
% 7.25/1.51  --instantiation_flag                    true
% 7.25/1.51  --inst_sos_flag                         false
% 7.25/1.51  --inst_sos_phase                        true
% 7.25/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.51  --inst_lit_sel_side                     num_symb
% 7.25/1.51  --inst_solver_per_active                1400
% 7.25/1.51  --inst_solver_calls_frac                1.
% 7.25/1.51  --inst_passive_queue_type               priority_queues
% 7.25/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.51  --inst_passive_queues_freq              [25;2]
% 7.25/1.51  --inst_dismatching                      true
% 7.25/1.51  --inst_eager_unprocessed_to_passive     true
% 7.25/1.51  --inst_prop_sim_given                   true
% 7.25/1.51  --inst_prop_sim_new                     false
% 7.25/1.51  --inst_subs_new                         false
% 7.25/1.51  --inst_eq_res_simp                      false
% 7.25/1.51  --inst_subs_given                       false
% 7.25/1.51  --inst_orphan_elimination               true
% 7.25/1.51  --inst_learning_loop_flag               true
% 7.25/1.51  --inst_learning_start                   3000
% 7.25/1.51  --inst_learning_factor                  2
% 7.25/1.51  --inst_start_prop_sim_after_learn       3
% 7.25/1.51  --inst_sel_renew                        solver
% 7.25/1.51  --inst_lit_activity_flag                true
% 7.25/1.51  --inst_restr_to_given                   false
% 7.25/1.51  --inst_activity_threshold               500
% 7.25/1.51  --inst_out_proof                        true
% 7.25/1.51  
% 7.25/1.51  ------ Resolution Options
% 7.25/1.51  
% 7.25/1.51  --resolution_flag                       true
% 7.25/1.51  --res_lit_sel                           adaptive
% 7.25/1.51  --res_lit_sel_side                      none
% 7.25/1.51  --res_ordering                          kbo
% 7.25/1.51  --res_to_prop_solver                    active
% 7.25/1.51  --res_prop_simpl_new                    false
% 7.25/1.51  --res_prop_simpl_given                  true
% 7.25/1.51  --res_passive_queue_type                priority_queues
% 7.25/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.51  --res_passive_queues_freq               [15;5]
% 7.25/1.51  --res_forward_subs                      full
% 7.25/1.51  --res_backward_subs                     full
% 7.25/1.51  --res_forward_subs_resolution           true
% 7.25/1.51  --res_backward_subs_resolution          true
% 7.25/1.51  --res_orphan_elimination                true
% 7.25/1.51  --res_time_limit                        2.
% 7.25/1.51  --res_out_proof                         true
% 7.25/1.51  
% 7.25/1.51  ------ Superposition Options
% 7.25/1.51  
% 7.25/1.51  --superposition_flag                    true
% 7.25/1.51  --sup_passive_queue_type                priority_queues
% 7.25/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.51  --demod_completeness_check              fast
% 7.25/1.51  --demod_use_ground                      true
% 7.25/1.51  --sup_to_prop_solver                    passive
% 7.25/1.51  --sup_prop_simpl_new                    true
% 7.25/1.51  --sup_prop_simpl_given                  true
% 7.25/1.51  --sup_fun_splitting                     false
% 7.25/1.51  --sup_smt_interval                      50000
% 7.25/1.51  
% 7.25/1.51  ------ Superposition Simplification Setup
% 7.25/1.51  
% 7.25/1.51  --sup_indices_passive                   []
% 7.25/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.51  --sup_full_bw                           [BwDemod]
% 7.25/1.51  --sup_immed_triv                        [TrivRules]
% 7.25/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.51  --sup_immed_bw_main                     []
% 7.25/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.51  
% 7.25/1.51  ------ Combination Options
% 7.25/1.51  
% 7.25/1.51  --comb_res_mult                         3
% 7.25/1.51  --comb_sup_mult                         2
% 7.25/1.51  --comb_inst_mult                        10
% 7.25/1.51  
% 7.25/1.51  ------ Debug Options
% 7.25/1.51  
% 7.25/1.51  --dbg_backtrace                         false
% 7.25/1.51  --dbg_dump_prop_clauses                 false
% 7.25/1.51  --dbg_dump_prop_clauses_file            -
% 7.25/1.51  --dbg_out_stat                          false
% 7.25/1.51  ------ Parsing...
% 7.25/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.25/1.51  
% 7.25/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.25/1.51  
% 7.25/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.25/1.51  
% 7.25/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.25/1.51  ------ Proving...
% 7.25/1.51  ------ Problem Properties 
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  clauses                                 18
% 7.25/1.51  conjectures                             1
% 7.25/1.51  EPR                                     2
% 7.25/1.51  Horn                                    15
% 7.25/1.51  unary                                   8
% 7.25/1.51  binary                                  5
% 7.25/1.51  lits                                    37
% 7.25/1.51  lits eq                                 12
% 7.25/1.51  fd_pure                                 0
% 7.25/1.51  fd_pseudo                               0
% 7.25/1.51  fd_cond                                 0
% 7.25/1.51  fd_pseudo_cond                          1
% 7.25/1.51  AC symbols                              0
% 7.25/1.51  
% 7.25/1.51  ------ Schedule dynamic 5 is on 
% 7.25/1.51  
% 7.25/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  ------ 
% 7.25/1.51  Current options:
% 7.25/1.51  ------ 
% 7.25/1.51  
% 7.25/1.51  ------ Input Options
% 7.25/1.51  
% 7.25/1.51  --out_options                           all
% 7.25/1.51  --tptp_safe_out                         true
% 7.25/1.51  --problem_path                          ""
% 7.25/1.51  --include_path                          ""
% 7.25/1.51  --clausifier                            res/vclausify_rel
% 7.25/1.51  --clausifier_options                    --mode clausify
% 7.25/1.51  --stdin                                 false
% 7.25/1.51  --stats_out                             all
% 7.25/1.51  
% 7.25/1.51  ------ General Options
% 7.25/1.51  
% 7.25/1.51  --fof                                   false
% 7.25/1.51  --time_out_real                         305.
% 7.25/1.51  --time_out_virtual                      -1.
% 7.25/1.51  --symbol_type_check                     false
% 7.25/1.51  --clausify_out                          false
% 7.25/1.51  --sig_cnt_out                           false
% 7.25/1.51  --trig_cnt_out                          false
% 7.25/1.51  --trig_cnt_out_tolerance                1.
% 7.25/1.51  --trig_cnt_out_sk_spl                   false
% 7.25/1.51  --abstr_cl_out                          false
% 7.25/1.51  
% 7.25/1.51  ------ Global Options
% 7.25/1.51  
% 7.25/1.51  --schedule                              default
% 7.25/1.51  --add_important_lit                     false
% 7.25/1.51  --prop_solver_per_cl                    1000
% 7.25/1.51  --min_unsat_core                        false
% 7.25/1.51  --soft_assumptions                      false
% 7.25/1.51  --soft_lemma_size                       3
% 7.25/1.51  --prop_impl_unit_size                   0
% 7.25/1.51  --prop_impl_unit                        []
% 7.25/1.51  --share_sel_clauses                     true
% 7.25/1.51  --reset_solvers                         false
% 7.25/1.51  --bc_imp_inh                            [conj_cone]
% 7.25/1.51  --conj_cone_tolerance                   3.
% 7.25/1.51  --extra_neg_conj                        none
% 7.25/1.51  --large_theory_mode                     true
% 7.25/1.51  --prolific_symb_bound                   200
% 7.25/1.51  --lt_threshold                          2000
% 7.25/1.51  --clause_weak_htbl                      true
% 7.25/1.51  --gc_record_bc_elim                     false
% 7.25/1.51  
% 7.25/1.51  ------ Preprocessing Options
% 7.25/1.51  
% 7.25/1.51  --preprocessing_flag                    true
% 7.25/1.51  --time_out_prep_mult                    0.1
% 7.25/1.51  --splitting_mode                        input
% 7.25/1.51  --splitting_grd                         true
% 7.25/1.51  --splitting_cvd                         false
% 7.25/1.51  --splitting_cvd_svl                     false
% 7.25/1.51  --splitting_nvd                         32
% 7.25/1.51  --sub_typing                            true
% 7.25/1.51  --prep_gs_sim                           true
% 7.25/1.51  --prep_unflatten                        true
% 7.25/1.51  --prep_res_sim                          true
% 7.25/1.51  --prep_upred                            true
% 7.25/1.51  --prep_sem_filter                       exhaustive
% 7.25/1.51  --prep_sem_filter_out                   false
% 7.25/1.51  --pred_elim                             true
% 7.25/1.51  --res_sim_input                         true
% 7.25/1.51  --eq_ax_congr_red                       true
% 7.25/1.51  --pure_diseq_elim                       true
% 7.25/1.51  --brand_transform                       false
% 7.25/1.51  --non_eq_to_eq                          false
% 7.25/1.51  --prep_def_merge                        true
% 7.25/1.51  --prep_def_merge_prop_impl              false
% 7.25/1.51  --prep_def_merge_mbd                    true
% 7.25/1.51  --prep_def_merge_tr_red                 false
% 7.25/1.51  --prep_def_merge_tr_cl                  false
% 7.25/1.51  --smt_preprocessing                     true
% 7.25/1.51  --smt_ac_axioms                         fast
% 7.25/1.51  --preprocessed_out                      false
% 7.25/1.51  --preprocessed_stats                    false
% 7.25/1.51  
% 7.25/1.51  ------ Abstraction refinement Options
% 7.25/1.51  
% 7.25/1.51  --abstr_ref                             []
% 7.25/1.51  --abstr_ref_prep                        false
% 7.25/1.51  --abstr_ref_until_sat                   false
% 7.25/1.51  --abstr_ref_sig_restrict                funpre
% 7.25/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.51  --abstr_ref_under                       []
% 7.25/1.51  
% 7.25/1.51  ------ SAT Options
% 7.25/1.51  
% 7.25/1.51  --sat_mode                              false
% 7.25/1.51  --sat_fm_restart_options                ""
% 7.25/1.51  --sat_gr_def                            false
% 7.25/1.51  --sat_epr_types                         true
% 7.25/1.51  --sat_non_cyclic_types                  false
% 7.25/1.51  --sat_finite_models                     false
% 7.25/1.51  --sat_fm_lemmas                         false
% 7.25/1.51  --sat_fm_prep                           false
% 7.25/1.51  --sat_fm_uc_incr                        true
% 7.25/1.51  --sat_out_model                         small
% 7.25/1.51  --sat_out_clauses                       false
% 7.25/1.51  
% 7.25/1.51  ------ QBF Options
% 7.25/1.51  
% 7.25/1.51  --qbf_mode                              false
% 7.25/1.51  --qbf_elim_univ                         false
% 7.25/1.51  --qbf_dom_inst                          none
% 7.25/1.51  --qbf_dom_pre_inst                      false
% 7.25/1.51  --qbf_sk_in                             false
% 7.25/1.51  --qbf_pred_elim                         true
% 7.25/1.51  --qbf_split                             512
% 7.25/1.51  
% 7.25/1.51  ------ BMC1 Options
% 7.25/1.51  
% 7.25/1.51  --bmc1_incremental                      false
% 7.25/1.51  --bmc1_axioms                           reachable_all
% 7.25/1.51  --bmc1_min_bound                        0
% 7.25/1.51  --bmc1_max_bound                        -1
% 7.25/1.51  --bmc1_max_bound_default                -1
% 7.25/1.51  --bmc1_symbol_reachability              true
% 7.25/1.51  --bmc1_property_lemmas                  false
% 7.25/1.51  --bmc1_k_induction                      false
% 7.25/1.51  --bmc1_non_equiv_states                 false
% 7.25/1.51  --bmc1_deadlock                         false
% 7.25/1.51  --bmc1_ucm                              false
% 7.25/1.51  --bmc1_add_unsat_core                   none
% 7.25/1.51  --bmc1_unsat_core_children              false
% 7.25/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.51  --bmc1_out_stat                         full
% 7.25/1.51  --bmc1_ground_init                      false
% 7.25/1.51  --bmc1_pre_inst_next_state              false
% 7.25/1.51  --bmc1_pre_inst_state                   false
% 7.25/1.51  --bmc1_pre_inst_reach_state             false
% 7.25/1.51  --bmc1_out_unsat_core                   false
% 7.25/1.51  --bmc1_aig_witness_out                  false
% 7.25/1.51  --bmc1_verbose                          false
% 7.25/1.51  --bmc1_dump_clauses_tptp                false
% 7.25/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.51  --bmc1_dump_file                        -
% 7.25/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.51  --bmc1_ucm_extend_mode                  1
% 7.25/1.51  --bmc1_ucm_init_mode                    2
% 7.25/1.51  --bmc1_ucm_cone_mode                    none
% 7.25/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.51  --bmc1_ucm_relax_model                  4
% 7.25/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.51  --bmc1_ucm_layered_model                none
% 7.25/1.51  --bmc1_ucm_max_lemma_size               10
% 7.25/1.51  
% 7.25/1.51  ------ AIG Options
% 7.25/1.51  
% 7.25/1.51  --aig_mode                              false
% 7.25/1.51  
% 7.25/1.51  ------ Instantiation Options
% 7.25/1.51  
% 7.25/1.51  --instantiation_flag                    true
% 7.25/1.51  --inst_sos_flag                         false
% 7.25/1.51  --inst_sos_phase                        true
% 7.25/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.51  --inst_lit_sel_side                     none
% 7.25/1.51  --inst_solver_per_active                1400
% 7.25/1.51  --inst_solver_calls_frac                1.
% 7.25/1.51  --inst_passive_queue_type               priority_queues
% 7.25/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.51  --inst_passive_queues_freq              [25;2]
% 7.25/1.51  --inst_dismatching                      true
% 7.25/1.51  --inst_eager_unprocessed_to_passive     true
% 7.25/1.51  --inst_prop_sim_given                   true
% 7.25/1.51  --inst_prop_sim_new                     false
% 7.25/1.51  --inst_subs_new                         false
% 7.25/1.51  --inst_eq_res_simp                      false
% 7.25/1.51  --inst_subs_given                       false
% 7.25/1.51  --inst_orphan_elimination               true
% 7.25/1.51  --inst_learning_loop_flag               true
% 7.25/1.51  --inst_learning_start                   3000
% 7.25/1.51  --inst_learning_factor                  2
% 7.25/1.51  --inst_start_prop_sim_after_learn       3
% 7.25/1.51  --inst_sel_renew                        solver
% 7.25/1.51  --inst_lit_activity_flag                true
% 7.25/1.51  --inst_restr_to_given                   false
% 7.25/1.51  --inst_activity_threshold               500
% 7.25/1.51  --inst_out_proof                        true
% 7.25/1.51  
% 7.25/1.51  ------ Resolution Options
% 7.25/1.51  
% 7.25/1.51  --resolution_flag                       false
% 7.25/1.51  --res_lit_sel                           adaptive
% 7.25/1.51  --res_lit_sel_side                      none
% 7.25/1.51  --res_ordering                          kbo
% 7.25/1.51  --res_to_prop_solver                    active
% 7.25/1.51  --res_prop_simpl_new                    false
% 7.25/1.51  --res_prop_simpl_given                  true
% 7.25/1.51  --res_passive_queue_type                priority_queues
% 7.25/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.51  --res_passive_queues_freq               [15;5]
% 7.25/1.51  --res_forward_subs                      full
% 7.25/1.51  --res_backward_subs                     full
% 7.25/1.51  --res_forward_subs_resolution           true
% 7.25/1.51  --res_backward_subs_resolution          true
% 7.25/1.51  --res_orphan_elimination                true
% 7.25/1.51  --res_time_limit                        2.
% 7.25/1.51  --res_out_proof                         true
% 7.25/1.51  
% 7.25/1.51  ------ Superposition Options
% 7.25/1.51  
% 7.25/1.51  --superposition_flag                    true
% 7.25/1.51  --sup_passive_queue_type                priority_queues
% 7.25/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.51  --demod_completeness_check              fast
% 7.25/1.51  --demod_use_ground                      true
% 7.25/1.51  --sup_to_prop_solver                    passive
% 7.25/1.51  --sup_prop_simpl_new                    true
% 7.25/1.51  --sup_prop_simpl_given                  true
% 7.25/1.51  --sup_fun_splitting                     false
% 7.25/1.51  --sup_smt_interval                      50000
% 7.25/1.51  
% 7.25/1.51  ------ Superposition Simplification Setup
% 7.25/1.51  
% 7.25/1.51  --sup_indices_passive                   []
% 7.25/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.51  --sup_full_bw                           [BwDemod]
% 7.25/1.51  --sup_immed_triv                        [TrivRules]
% 7.25/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.51  --sup_immed_bw_main                     []
% 7.25/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.51  
% 7.25/1.51  ------ Combination Options
% 7.25/1.51  
% 7.25/1.51  --comb_res_mult                         3
% 7.25/1.51  --comb_sup_mult                         2
% 7.25/1.51  --comb_inst_mult                        10
% 7.25/1.51  
% 7.25/1.51  ------ Debug Options
% 7.25/1.51  
% 7.25/1.51  --dbg_backtrace                         false
% 7.25/1.51  --dbg_dump_prop_clauses                 false
% 7.25/1.51  --dbg_dump_prop_clauses_file            -
% 7.25/1.51  --dbg_out_stat                          false
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  ------ Proving...
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  % SZS status Theorem for theBenchmark.p
% 7.25/1.51  
% 7.25/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.25/1.51  
% 7.25/1.51  fof(f3,axiom,(
% 7.25/1.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f14,plain,(
% 7.25/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.25/1.51    inference(ennf_transformation,[],[f3])).
% 7.25/1.51  
% 7.25/1.51  fof(f34,plain,(
% 7.25/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f14])).
% 7.25/1.51  
% 7.25/1.51  fof(f1,axiom,(
% 7.25/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f21,plain,(
% 7.25/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.25/1.51    inference(nnf_transformation,[],[f1])).
% 7.25/1.51  
% 7.25/1.51  fof(f22,plain,(
% 7.25/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.25/1.51    inference(flattening,[],[f21])).
% 7.25/1.51  
% 7.25/1.51  fof(f31,plain,(
% 7.25/1.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.25/1.51    inference(cnf_transformation,[],[f22])).
% 7.25/1.51  
% 7.25/1.51  fof(f50,plain,(
% 7.25/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.25/1.51    inference(equality_resolution,[],[f31])).
% 7.25/1.51  
% 7.25/1.51  fof(f7,axiom,(
% 7.25/1.51    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f16,plain,(
% 7.25/1.51    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.25/1.51    inference(ennf_transformation,[],[f7])).
% 7.25/1.51  
% 7.25/1.51  fof(f39,plain,(
% 7.25/1.51    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f16])).
% 7.25/1.51  
% 7.25/1.51  fof(f10,axiom,(
% 7.25/1.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f48,plain,(
% 7.25/1.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 7.25/1.51    inference(cnf_transformation,[],[f10])).
% 7.25/1.51  
% 7.25/1.51  fof(f9,axiom,(
% 7.25/1.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f18,plain,(
% 7.25/1.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 7.25/1.51    inference(ennf_transformation,[],[f9])).
% 7.25/1.51  
% 7.25/1.51  fof(f19,plain,(
% 7.25/1.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 7.25/1.51    inference(flattening,[],[f18])).
% 7.25/1.51  
% 7.25/1.51  fof(f23,plain,(
% 7.25/1.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.25/1.51    inference(nnf_transformation,[],[f19])).
% 7.25/1.51  
% 7.25/1.51  fof(f24,plain,(
% 7.25/1.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.25/1.51    inference(flattening,[],[f23])).
% 7.25/1.51  
% 7.25/1.51  fof(f25,plain,(
% 7.25/1.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.25/1.51    inference(rectify,[],[f24])).
% 7.25/1.51  
% 7.25/1.51  fof(f26,plain,(
% 7.25/1.51    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 7.25/1.51    introduced(choice_axiom,[])).
% 7.25/1.51  
% 7.25/1.51  fof(f27,plain,(
% 7.25/1.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.25/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 7.25/1.51  
% 7.25/1.51  fof(f41,plain,(
% 7.25/1.51    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f27])).
% 7.25/1.51  
% 7.25/1.51  fof(f58,plain,(
% 7.25/1.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 7.25/1.51    inference(equality_resolution,[],[f41])).
% 7.25/1.51  
% 7.25/1.51  fof(f2,axiom,(
% 7.25/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f13,plain,(
% 7.25/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.25/1.51    inference(ennf_transformation,[],[f2])).
% 7.25/1.51  
% 7.25/1.51  fof(f33,plain,(
% 7.25/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f13])).
% 7.25/1.51  
% 7.25/1.51  fof(f4,axiom,(
% 7.25/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f15,plain,(
% 7.25/1.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.25/1.51    inference(ennf_transformation,[],[f4])).
% 7.25/1.51  
% 7.25/1.51  fof(f35,plain,(
% 7.25/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f15])).
% 7.25/1.51  
% 7.25/1.51  fof(f6,axiom,(
% 7.25/1.51    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f37,plain,(
% 7.25/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f6])).
% 7.25/1.51  
% 7.25/1.51  fof(f5,axiom,(
% 7.25/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f36,plain,(
% 7.25/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.25/1.51    inference(cnf_transformation,[],[f5])).
% 7.25/1.51  
% 7.25/1.51  fof(f38,plain,(
% 7.25/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 7.25/1.51    inference(cnf_transformation,[],[f6])).
% 7.25/1.51  
% 7.25/1.51  fof(f8,axiom,(
% 7.25/1.51    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f17,plain,(
% 7.25/1.51    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.25/1.51    inference(ennf_transformation,[],[f8])).
% 7.25/1.51  
% 7.25/1.51  fof(f40,plain,(
% 7.25/1.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f17])).
% 7.25/1.51  
% 7.25/1.51  fof(f32,plain,(
% 7.25/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.25/1.51    inference(cnf_transformation,[],[f22])).
% 7.25/1.51  
% 7.25/1.51  fof(f30,plain,(
% 7.25/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.25/1.51    inference(cnf_transformation,[],[f22])).
% 7.25/1.51  
% 7.25/1.51  fof(f51,plain,(
% 7.25/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.25/1.51    inference(equality_resolution,[],[f30])).
% 7.25/1.51  
% 7.25/1.51  fof(f11,conjecture,(
% 7.25/1.51    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 7.25/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.51  
% 7.25/1.51  fof(f12,negated_conjecture,(
% 7.25/1.51    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 7.25/1.51    inference(negated_conjecture,[],[f11])).
% 7.25/1.51  
% 7.25/1.51  fof(f20,plain,(
% 7.25/1.51    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 7.25/1.51    inference(ennf_transformation,[],[f12])).
% 7.25/1.51  
% 7.25/1.51  fof(f28,plain,(
% 7.25/1.51    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 7.25/1.51    introduced(choice_axiom,[])).
% 7.25/1.51  
% 7.25/1.51  fof(f29,plain,(
% 7.25/1.51    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 7.25/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).
% 7.25/1.51  
% 7.25/1.51  fof(f49,plain,(
% 7.25/1.51    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 7.25/1.51    inference(cnf_transformation,[],[f29])).
% 7.25/1.51  
% 7.25/1.51  cnf(c_4,plain,
% 7.25/1.51      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.25/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_807,plain,
% 7.25/1.51      ( ~ r1_tarski(k2_xboole_0(k1_wellord2(sK2),X0),k2_zfmisc_1(sK2,sK2))
% 7.25/1.51      | r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_19457,plain,
% 7.25/1.51      ( ~ r1_tarski(k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))),k2_zfmisc_1(sK2,sK2))
% 7.25/1.51      | r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_807]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_1,plain,
% 7.25/1.51      ( r1_tarski(X0,X0) ),
% 7.25/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_719,plain,
% 7.25/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.25/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_9,plain,
% 7.25/1.51      ( ~ v1_relat_1(X0)
% 7.25/1.51      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 7.25/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_18,plain,
% 7.25/1.51      ( v1_relat_1(k1_wellord2(X0)) ),
% 7.25/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_272,plain,
% 7.25/1.51      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 7.25/1.51      | k1_wellord2(X1) != X0 ),
% 7.25/1.51      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_273,plain,
% 7.25/1.51      ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = k3_relat_1(k1_wellord2(X0)) ),
% 7.25/1.51      inference(unflattening,[status(thm)],[c_272]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_17,plain,
% 7.25/1.51      ( ~ v1_relat_1(k1_wellord2(X0))
% 7.25/1.51      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 7.25/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_109,plain,
% 7.25/1.51      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 7.25/1.51      inference(global_propositional_subsumption,
% 7.25/1.51                [status(thm)],
% 7.25/1.51                [c_17,c_18]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_729,plain,
% 7.25/1.51      ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
% 7.25/1.51      inference(light_normalisation,[status(thm)],[c_273,c_109]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_3,plain,
% 7.25/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.25/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_718,plain,
% 7.25/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.25/1.51      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 7.25/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_1966,plain,
% 7.25/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.25/1.51      | r1_tarski(X0,k2_relat_1(k1_wellord2(X1))) != iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_729,c_718]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_7434,plain,
% 7.25/1.51      ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_719,c_1966]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_5,plain,
% 7.25/1.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.25/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_716,plain,
% 7.25/1.51      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.25/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_7609,plain,
% 7.25/1.51      ( k2_xboole_0(k2_relat_1(k1_wellord2(X0)),X0) = X0 ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_7434,c_716]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_8,plain,
% 7.25/1.51      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
% 7.25/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_6,plain,
% 7.25/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.25/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_715,plain,
% 7.25/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.25/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_1019,plain,
% 7.25/1.51      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),X1)) = iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_8,c_715]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_1146,plain,
% 7.25/1.51      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_729,c_1019]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_1558,plain,
% 7.25/1.51      ( k2_xboole_0(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(X0,X1) ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_1146,c_716]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_7,plain,
% 7.25/1.51      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X1,X2)) ),
% 7.25/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_717,plain,
% 7.25/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.25/1.51      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 7.25/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_1770,plain,
% 7.25/1.51      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_715,c_717]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_2317,plain,
% 7.25/1.51      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_xboole_0(k2_zfmisc_1(X0,k2_xboole_0(X1,X2)),X3)) = iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_7,c_1770]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_3125,plain,
% 7.25/1.51      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X1),k2_zfmisc_1(X0,k2_xboole_0(X1,X2))) = iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_1558,c_2317]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_8527,plain,
% 7.25/1.51      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X1))),k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_7609,c_3125]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_8662,plain,
% 7.25/1.51      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X1))),k2_zfmisc_1(X0,X1)) ),
% 7.25/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_8527]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_8664,plain,
% 7.25/1.51      ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))),k2_zfmisc_1(sK2,sK2)) ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_8662]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_451,plain,
% 7.25/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.25/1.51      theory(equality) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_846,plain,
% 7.25/1.51      ( ~ r1_tarski(X0,X1)
% 7.25/1.51      | r1_tarski(k2_xboole_0(k1_wellord2(sK2),X2),k2_zfmisc_1(sK2,sK2))
% 7.25/1.51      | k2_zfmisc_1(sK2,sK2) != X1
% 7.25/1.51      | k2_xboole_0(k1_wellord2(sK2),X2) != X0 ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_451]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_1056,plain,
% 7.25/1.51      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.25/1.51      | r1_tarski(k2_xboole_0(k1_wellord2(sK2),X3),k2_zfmisc_1(sK2,sK2))
% 7.25/1.51      | k2_zfmisc_1(sK2,sK2) != k2_zfmisc_1(X1,X2)
% 7.25/1.51      | k2_xboole_0(k1_wellord2(sK2),X3) != X0 ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_846]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_3856,plain,
% 7.25/1.51      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))),k2_zfmisc_1(X0,X1))
% 7.25/1.51      | r1_tarski(k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))),k2_zfmisc_1(sK2,sK2))
% 7.25/1.51      | k2_zfmisc_1(sK2,sK2) != k2_zfmisc_1(X0,X1)
% 7.25/1.51      | k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))) ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_1056]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_3858,plain,
% 7.25/1.51      ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))),k2_zfmisc_1(sK2,sK2))
% 7.25/1.51      | r1_tarski(k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))),k2_zfmisc_1(sK2,sK2))
% 7.25/1.51      | k2_zfmisc_1(sK2,sK2) != k2_zfmisc_1(sK2,sK2)
% 7.25/1.51      | k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))) ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_3856]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_10,plain,
% 7.25/1.51      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 7.25/1.51      | ~ v1_relat_1(X0) ),
% 7.25/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_263,plain,
% 7.25/1.51      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 7.25/1.51      | k1_wellord2(X1) != X0 ),
% 7.25/1.51      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_264,plain,
% 7.25/1.51      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) ),
% 7.25/1.51      inference(unflattening,[status(thm)],[c_263]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_709,plain,
% 7.25/1.51      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = iProver_top ),
% 7.25/1.51      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_902,plain,
% 7.25/1.51      ( k2_xboole_0(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) = k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
% 7.25/1.51      inference(superposition,[status(thm)],[c_709,c_716]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_914,plain,
% 7.25/1.51      ( k2_xboole_0(k1_wellord2(sK2),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2)))) = k2_zfmisc_1(k1_relat_1(k1_wellord2(sK2)),k2_relat_1(k1_wellord2(sK2))) ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_902]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_453,plain,
% 7.25/1.51      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.25/1.51      theory(equality) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_464,plain,
% 7.25/1.51      ( k2_zfmisc_1(sK2,sK2) = k2_zfmisc_1(sK2,sK2) | sK2 != sK2 ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_453]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_0,plain,
% 7.25/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.25/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_68,plain,
% 7.25/1.51      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_2,plain,
% 7.25/1.51      ( r1_tarski(X0,X0) ),
% 7.25/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_64,plain,
% 7.25/1.51      ( r1_tarski(sK2,sK2) ),
% 7.25/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(c_19,negated_conjecture,
% 7.25/1.51      ( ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
% 7.25/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.25/1.51  
% 7.25/1.51  cnf(contradiction,plain,
% 7.25/1.51      ( $false ),
% 7.25/1.51      inference(minisat,
% 7.25/1.51                [status(thm)],
% 7.25/1.51                [c_19457,c_8664,c_3858,c_914,c_464,c_68,c_64,c_19]) ).
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.25/1.51  
% 7.25/1.51  ------                               Statistics
% 7.25/1.51  
% 7.25/1.51  ------ General
% 7.25/1.51  
% 7.25/1.51  abstr_ref_over_cycles:                  0
% 7.25/1.51  abstr_ref_under_cycles:                 0
% 7.25/1.51  gc_basic_clause_elim:                   0
% 7.25/1.51  forced_gc_time:                         0
% 7.25/1.51  parsing_time:                           0.009
% 7.25/1.51  unif_index_cands_time:                  0.
% 7.25/1.51  unif_index_add_time:                    0.
% 7.25/1.51  orderings_time:                         0.
% 7.25/1.51  out_proof_time:                         0.008
% 7.25/1.51  total_time:                             0.571
% 7.25/1.51  num_of_symbols:                         44
% 7.25/1.51  num_of_terms:                           25061
% 7.25/1.51  
% 7.25/1.51  ------ Preprocessing
% 7.25/1.51  
% 7.25/1.51  num_of_splits:                          0
% 7.25/1.51  num_of_split_atoms:                     0
% 7.25/1.51  num_of_reused_defs:                     0
% 7.25/1.51  num_eq_ax_congr_red:                    4
% 7.25/1.51  num_of_sem_filtered_clauses:            1
% 7.25/1.51  num_of_subtypes:                        0
% 7.25/1.51  monotx_restored_types:                  0
% 7.25/1.51  sat_num_of_epr_types:                   0
% 7.25/1.51  sat_num_of_non_cyclic_types:            0
% 7.25/1.51  sat_guarded_non_collapsed_types:        0
% 7.25/1.51  num_pure_diseq_elim:                    0
% 7.25/1.51  simp_replaced_by:                       0
% 7.25/1.51  res_preprocessed:                       100
% 7.25/1.51  prep_upred:                             0
% 7.25/1.51  prep_unflattend:                        6
% 7.25/1.51  smt_new_axioms:                         0
% 7.25/1.51  pred_elim_cands:                        2
% 7.25/1.51  pred_elim:                              1
% 7.25/1.51  pred_elim_cl:                           1
% 7.25/1.51  pred_elim_cycles:                       3
% 7.25/1.51  merged_defs:                            0
% 7.25/1.51  merged_defs_ncl:                        0
% 7.25/1.51  bin_hyper_res:                          0
% 7.25/1.51  prep_cycles:                            4
% 7.25/1.51  pred_elim_time:                         0.003
% 7.25/1.51  splitting_time:                         0.
% 7.25/1.51  sem_filter_time:                        0.
% 7.25/1.51  monotx_time:                            0.
% 7.25/1.51  subtype_inf_time:                       0.
% 7.25/1.51  
% 7.25/1.51  ------ Problem properties
% 7.25/1.51  
% 7.25/1.51  clauses:                                18
% 7.25/1.51  conjectures:                            1
% 7.25/1.51  epr:                                    2
% 7.25/1.51  horn:                                   15
% 7.25/1.51  ground:                                 1
% 7.25/1.51  unary:                                  8
% 7.25/1.51  binary:                                 5
% 7.25/1.51  lits:                                   37
% 7.25/1.51  lits_eq:                                12
% 7.25/1.51  fd_pure:                                0
% 7.25/1.51  fd_pseudo:                              0
% 7.25/1.51  fd_cond:                                0
% 7.25/1.51  fd_pseudo_cond:                         1
% 7.25/1.51  ac_symbols:                             0
% 7.25/1.51  
% 7.25/1.51  ------ Propositional Solver
% 7.25/1.51  
% 7.25/1.51  prop_solver_calls:                      32
% 7.25/1.51  prop_fast_solver_calls:                 624
% 7.25/1.51  smt_solver_calls:                       0
% 7.25/1.51  smt_fast_solver_calls:                  0
% 7.25/1.51  prop_num_of_clauses:                    9380
% 7.25/1.51  prop_preprocess_simplified:             11211
% 7.25/1.51  prop_fo_subsumed:                       1
% 7.25/1.51  prop_solver_time:                       0.
% 7.25/1.51  smt_solver_time:                        0.
% 7.25/1.51  smt_fast_solver_time:                   0.
% 7.25/1.51  prop_fast_solver_time:                  0.
% 7.25/1.51  prop_unsat_core_time:                   0.001
% 7.25/1.51  
% 7.25/1.51  ------ QBF
% 7.25/1.51  
% 7.25/1.51  qbf_q_res:                              0
% 7.25/1.51  qbf_num_tautologies:                    0
% 7.25/1.51  qbf_prep_cycles:                        0
% 7.25/1.51  
% 7.25/1.51  ------ BMC1
% 7.25/1.51  
% 7.25/1.51  bmc1_current_bound:                     -1
% 7.25/1.51  bmc1_last_solved_bound:                 -1
% 7.25/1.51  bmc1_unsat_core_size:                   -1
% 7.25/1.51  bmc1_unsat_core_parents_size:           -1
% 7.25/1.51  bmc1_merge_next_fun:                    0
% 7.25/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.25/1.51  
% 7.25/1.51  ------ Instantiation
% 7.25/1.51  
% 7.25/1.51  inst_num_of_clauses:                    1685
% 7.25/1.51  inst_num_in_passive:                    542
% 7.25/1.51  inst_num_in_active:                     608
% 7.25/1.51  inst_num_in_unprocessed:                534
% 7.25/1.51  inst_num_of_loops:                      619
% 7.25/1.51  inst_num_of_learning_restarts:          0
% 7.25/1.51  inst_num_moves_active_passive:          5
% 7.25/1.51  inst_lit_activity:                      0
% 7.25/1.51  inst_lit_activity_moves:                0
% 7.25/1.51  inst_num_tautologies:                   0
% 7.25/1.51  inst_num_prop_implied:                  0
% 7.25/1.51  inst_num_existing_simplified:           0
% 7.25/1.51  inst_num_eq_res_simplified:             0
% 7.25/1.51  inst_num_child_elim:                    0
% 7.25/1.51  inst_num_of_dismatching_blockings:      695
% 7.25/1.51  inst_num_of_non_proper_insts:           2139
% 7.25/1.51  inst_num_of_duplicates:                 0
% 7.25/1.51  inst_inst_num_from_inst_to_res:         0
% 7.25/1.51  inst_dismatching_checking_time:         0.
% 7.25/1.51  
% 7.25/1.51  ------ Resolution
% 7.25/1.51  
% 7.25/1.51  res_num_of_clauses:                     0
% 7.25/1.51  res_num_in_passive:                     0
% 7.25/1.51  res_num_in_active:                      0
% 7.25/1.51  res_num_of_loops:                       104
% 7.25/1.51  res_forward_subset_subsumed:            310
% 7.25/1.51  res_backward_subset_subsumed:           0
% 7.25/1.51  res_forward_subsumed:                   0
% 7.25/1.51  res_backward_subsumed:                  0
% 7.25/1.51  res_forward_subsumption_resolution:     0
% 7.25/1.51  res_backward_subsumption_resolution:    0
% 7.25/1.51  res_clause_to_clause_subsumption:       8982
% 7.25/1.51  res_orphan_elimination:                 0
% 7.25/1.51  res_tautology_del:                      126
% 7.25/1.51  res_num_eq_res_simplified:              0
% 7.25/1.51  res_num_sel_changes:                    0
% 7.25/1.51  res_moves_from_active_to_pass:          0
% 7.25/1.51  
% 7.25/1.51  ------ Superposition
% 7.25/1.51  
% 7.25/1.51  sup_time_total:                         0.
% 7.25/1.51  sup_time_generating:                    0.
% 7.25/1.51  sup_time_sim_full:                      0.
% 7.25/1.51  sup_time_sim_immed:                     0.
% 7.25/1.51  
% 7.25/1.51  sup_num_of_clauses:                     1488
% 7.25/1.51  sup_num_in_active:                      121
% 7.25/1.51  sup_num_in_passive:                     1367
% 7.25/1.51  sup_num_of_loops:                       122
% 7.25/1.51  sup_fw_superposition:                   1207
% 7.25/1.51  sup_bw_superposition:                   1115
% 7.25/1.51  sup_immediate_simplified:               287
% 7.25/1.51  sup_given_eliminated:                   0
% 7.25/1.51  comparisons_done:                       0
% 7.25/1.51  comparisons_avoided:                    0
% 7.25/1.51  
% 7.25/1.51  ------ Simplifications
% 7.25/1.51  
% 7.25/1.51  
% 7.25/1.51  sim_fw_subset_subsumed:                 0
% 7.25/1.51  sim_bw_subset_subsumed:                 0
% 7.25/1.51  sim_fw_subsumed:                        24
% 7.25/1.51  sim_bw_subsumed:                        0
% 7.25/1.51  sim_fw_subsumption_res:                 0
% 7.25/1.51  sim_bw_subsumption_res:                 0
% 7.25/1.51  sim_tautology_del:                      28
% 7.25/1.51  sim_eq_tautology_del:                   44
% 7.25/1.51  sim_eq_res_simp:                        0
% 7.25/1.51  sim_fw_demodulated:                     92
% 7.25/1.51  sim_bw_demodulated:                     1
% 7.25/1.51  sim_light_normalised:                   199
% 7.25/1.51  sim_joinable_taut:                      0
% 7.25/1.51  sim_joinable_simp:                      0
% 7.25/1.51  sim_ac_normalised:                      0
% 7.25/1.51  sim_smt_subsumption:                    0
% 7.25/1.51  
%------------------------------------------------------------------------------
