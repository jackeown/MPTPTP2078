%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:06 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 190 expanded)
%              Number of clauses        :   48 (  94 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  276 ( 560 expanded)
%              Number of equality atoms :  120 ( 195 expanded)
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
   => ( ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f22])).

fof(f36,plain,(
    v1_relat_1(sK5) ),
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
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
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
              ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,
    ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_249,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_468,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_254,plain,
    ( r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK3(X0_43,X1_43,X2_43)),X0_43)
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43)
    | ~ v1_relat_1(X2_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(X0_43)
    | k5_relat_1(X0_43,X1_43) = X2_43 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_464,plain,
    ( k5_relat_1(X0_43,X1_43) = X2_43
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK3(X0_43,X1_43,X2_43)),X0_43) = iProver_top
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43) = iProver_top
    | v1_relat_1(X2_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_163,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_164,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_44,k1_xboole_0)) ),
    inference(subtyping,[status(esa)],[c_164])).

cnf(c_471,plain,
    ( r2_hidden(X0_42,k3_xboole_0(X0_44,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_257,plain,
    ( k3_xboole_0(X0_44,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_478,plain,
    ( r2_hidden(X0_42,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_471,c_257])).

cnf(c_1163,plain,
    ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,k1_xboole_0),sK3(X0_43,X1_43,k1_xboole_0)),X0_43) = iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_464,c_478])).

cnf(c_5,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_33,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_35,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_44,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4034,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,k1_xboole_0),sK3(X0_43,X1_43,k1_xboole_0)),X0_43) = iProver_top
    | k5_relat_1(X0_43,X1_43) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1163,c_35,c_44])).

cnf(c_4035,plain,
    ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,k1_xboole_0),sK3(X0_43,X1_43,k1_xboole_0)),X0_43) = iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_4034])).

cnf(c_4044,plain,
    ( k5_relat_1(k1_xboole_0,X0_43) = k1_xboole_0
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4035,c_478])).

cnf(c_4233,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | k5_relat_1(k1_xboole_0,X0_43) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4044,c_35,c_44])).

cnf(c_4234,plain,
    ( k5_relat_1(k1_xboole_0,X0_43) = k1_xboole_0
    | v1_relat_1(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_4233])).

cnf(c_4239,plain,
    ( k5_relat_1(k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_468,c_4234])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_255,plain,
    ( r2_hidden(k4_tarski(sK3(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X1_43)
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43)
    | ~ v1_relat_1(X2_43)
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(X0_43)
    | k5_relat_1(X0_43,X1_43) = X2_43 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_463,plain,
    ( k5_relat_1(X0_43,X1_43) = X2_43
    | r2_hidden(k4_tarski(sK3(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X1_43) = iProver_top
    | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43) = iProver_top
    | v1_relat_1(X2_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_970,plain,
    ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
    | r2_hidden(k4_tarski(sK3(X0_43,X1_43,k1_xboole_0),sK2(X0_43,X1_43,k1_xboole_0)),X1_43) = iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_463,c_478])).

cnf(c_2678,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0_43,X1_43,k1_xboole_0),sK2(X0_43,X1_43,k1_xboole_0)),X1_43) = iProver_top
    | k5_relat_1(X0_43,X1_43) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_970,c_35,c_44])).

cnf(c_2679,plain,
    ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
    | r2_hidden(k4_tarski(sK3(X0_43,X1_43,k1_xboole_0),sK2(X0_43,X1_43,k1_xboole_0)),X1_43) = iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_2678])).

cnf(c_2688,plain,
    ( k5_relat_1(X0_43,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2679,c_478])).

cnf(c_2861,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | k5_relat_1(X0_43,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2688,c_35,c_44])).

cnf(c_2862,plain,
    ( k5_relat_1(X0_43,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_2861])).

cnf(c_2867,plain,
    ( k5_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_468,c_2862])).

cnf(c_262,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_681,plain,
    ( k5_relat_1(X0_43,X1_43) != X2_43
    | k1_xboole_0 != X2_43
    | k1_xboole_0 = k5_relat_1(X0_43,X1_43) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_1668,plain,
    ( k5_relat_1(k1_xboole_0,sK5) != X0_43
    | k1_xboole_0 != X0_43
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1669,plain,
    ( k5_relat_1(k1_xboole_0,sK5) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_583,plain,
    ( k5_relat_1(sK5,k1_xboole_0) != X0_43
    | k1_xboole_0 != X0_43
    | k1_xboole_0 = k5_relat_1(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_584,plain,
    ( k5_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_250,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_260,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_275,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4239,c_2867,c_1669,c_584,c_250,c_275])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.19/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/0.99  
% 2.19/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/0.99  
% 2.19/0.99  ------  iProver source info
% 2.19/0.99  
% 2.19/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.19/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/0.99  git: non_committed_changes: false
% 2.19/0.99  git: last_make_outside_of_git: false
% 2.19/0.99  
% 2.19/0.99  ------ 
% 2.19/0.99  
% 2.19/0.99  ------ Input Options
% 2.19/0.99  
% 2.19/0.99  --out_options                           all
% 2.19/0.99  --tptp_safe_out                         true
% 2.19/0.99  --problem_path                          ""
% 2.19/0.99  --include_path                          ""
% 2.19/0.99  --clausifier                            res/vclausify_rel
% 2.19/0.99  --clausifier_options                    --mode clausify
% 2.19/0.99  --stdin                                 false
% 2.19/0.99  --stats_out                             all
% 2.19/0.99  
% 2.19/0.99  ------ General Options
% 2.19/0.99  
% 2.19/0.99  --fof                                   false
% 2.19/0.99  --time_out_real                         305.
% 2.19/0.99  --time_out_virtual                      -1.
% 2.19/0.99  --symbol_type_check                     false
% 2.19/0.99  --clausify_out                          false
% 2.19/0.99  --sig_cnt_out                           false
% 2.19/0.99  --trig_cnt_out                          false
% 2.19/0.99  --trig_cnt_out_tolerance                1.
% 2.19/0.99  --trig_cnt_out_sk_spl                   false
% 2.19/0.99  --abstr_cl_out                          false
% 2.19/0.99  
% 2.19/0.99  ------ Global Options
% 2.19/0.99  
% 2.19/0.99  --schedule                              default
% 2.19/0.99  --add_important_lit                     false
% 2.19/0.99  --prop_solver_per_cl                    1000
% 2.19/0.99  --min_unsat_core                        false
% 2.19/0.99  --soft_assumptions                      false
% 2.19/0.99  --soft_lemma_size                       3
% 2.19/0.99  --prop_impl_unit_size                   0
% 2.19/0.99  --prop_impl_unit                        []
% 2.19/0.99  --share_sel_clauses                     true
% 2.19/0.99  --reset_solvers                         false
% 2.19/0.99  --bc_imp_inh                            [conj_cone]
% 2.19/0.99  --conj_cone_tolerance                   3.
% 2.19/0.99  --extra_neg_conj                        none
% 2.19/0.99  --large_theory_mode                     true
% 2.19/0.99  --prolific_symb_bound                   200
% 2.19/0.99  --lt_threshold                          2000
% 2.19/0.99  --clause_weak_htbl                      true
% 2.19/0.99  --gc_record_bc_elim                     false
% 2.19/0.99  
% 2.19/0.99  ------ Preprocessing Options
% 2.19/0.99  
% 2.19/0.99  --preprocessing_flag                    true
% 2.19/0.99  --time_out_prep_mult                    0.1
% 2.19/0.99  --splitting_mode                        input
% 2.19/0.99  --splitting_grd                         true
% 2.19/0.99  --splitting_cvd                         false
% 2.19/0.99  --splitting_cvd_svl                     false
% 2.19/0.99  --splitting_nvd                         32
% 2.19/0.99  --sub_typing                            true
% 2.19/0.99  --prep_gs_sim                           true
% 2.19/0.99  --prep_unflatten                        true
% 2.19/0.99  --prep_res_sim                          true
% 2.19/0.99  --prep_upred                            true
% 2.19/0.99  --prep_sem_filter                       exhaustive
% 2.19/0.99  --prep_sem_filter_out                   false
% 2.19/0.99  --pred_elim                             true
% 2.19/0.99  --res_sim_input                         true
% 2.19/0.99  --eq_ax_congr_red                       true
% 2.19/0.99  --pure_diseq_elim                       true
% 2.19/0.99  --brand_transform                       false
% 2.19/0.99  --non_eq_to_eq                          false
% 2.19/0.99  --prep_def_merge                        true
% 2.19/0.99  --prep_def_merge_prop_impl              false
% 2.19/0.99  --prep_def_merge_mbd                    true
% 2.19/0.99  --prep_def_merge_tr_red                 false
% 2.19/0.99  --prep_def_merge_tr_cl                  false
% 2.19/0.99  --smt_preprocessing                     true
% 2.19/0.99  --smt_ac_axioms                         fast
% 2.19/0.99  --preprocessed_out                      false
% 2.19/0.99  --preprocessed_stats                    false
% 2.19/0.99  
% 2.19/0.99  ------ Abstraction refinement Options
% 2.19/0.99  
% 2.19/0.99  --abstr_ref                             []
% 2.19/0.99  --abstr_ref_prep                        false
% 2.19/0.99  --abstr_ref_until_sat                   false
% 2.19/0.99  --abstr_ref_sig_restrict                funpre
% 2.19/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.99  --abstr_ref_under                       []
% 2.19/0.99  
% 2.19/0.99  ------ SAT Options
% 2.19/0.99  
% 2.19/0.99  --sat_mode                              false
% 2.19/0.99  --sat_fm_restart_options                ""
% 2.19/0.99  --sat_gr_def                            false
% 2.19/0.99  --sat_epr_types                         true
% 2.19/0.99  --sat_non_cyclic_types                  false
% 2.19/0.99  --sat_finite_models                     false
% 2.19/0.99  --sat_fm_lemmas                         false
% 2.19/0.99  --sat_fm_prep                           false
% 2.19/0.99  --sat_fm_uc_incr                        true
% 2.19/0.99  --sat_out_model                         small
% 2.19/0.99  --sat_out_clauses                       false
% 2.19/0.99  
% 2.19/0.99  ------ QBF Options
% 2.19/0.99  
% 2.19/0.99  --qbf_mode                              false
% 2.19/0.99  --qbf_elim_univ                         false
% 2.19/0.99  --qbf_dom_inst                          none
% 2.19/0.99  --qbf_dom_pre_inst                      false
% 2.19/0.99  --qbf_sk_in                             false
% 2.19/0.99  --qbf_pred_elim                         true
% 2.19/0.99  --qbf_split                             512
% 2.19/0.99  
% 2.19/0.99  ------ BMC1 Options
% 2.19/0.99  
% 2.19/0.99  --bmc1_incremental                      false
% 2.19/0.99  --bmc1_axioms                           reachable_all
% 2.19/0.99  --bmc1_min_bound                        0
% 2.19/0.99  --bmc1_max_bound                        -1
% 2.19/0.99  --bmc1_max_bound_default                -1
% 2.19/0.99  --bmc1_symbol_reachability              true
% 2.19/0.99  --bmc1_property_lemmas                  false
% 2.19/0.99  --bmc1_k_induction                      false
% 2.19/0.99  --bmc1_non_equiv_states                 false
% 2.19/0.99  --bmc1_deadlock                         false
% 2.19/0.99  --bmc1_ucm                              false
% 2.19/0.99  --bmc1_add_unsat_core                   none
% 2.19/0.99  --bmc1_unsat_core_children              false
% 2.19/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.99  --bmc1_out_stat                         full
% 2.19/0.99  --bmc1_ground_init                      false
% 2.19/0.99  --bmc1_pre_inst_next_state              false
% 2.19/0.99  --bmc1_pre_inst_state                   false
% 2.19/0.99  --bmc1_pre_inst_reach_state             false
% 2.19/0.99  --bmc1_out_unsat_core                   false
% 2.19/0.99  --bmc1_aig_witness_out                  false
% 2.19/0.99  --bmc1_verbose                          false
% 2.19/0.99  --bmc1_dump_clauses_tptp                false
% 2.19/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.99  --bmc1_dump_file                        -
% 2.19/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.99  --bmc1_ucm_extend_mode                  1
% 2.19/0.99  --bmc1_ucm_init_mode                    2
% 2.19/0.99  --bmc1_ucm_cone_mode                    none
% 2.19/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.99  --bmc1_ucm_relax_model                  4
% 2.19/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.99  --bmc1_ucm_layered_model                none
% 2.19/0.99  --bmc1_ucm_max_lemma_size               10
% 2.19/0.99  
% 2.19/0.99  ------ AIG Options
% 2.19/0.99  
% 2.19/0.99  --aig_mode                              false
% 2.19/0.99  
% 2.19/0.99  ------ Instantiation Options
% 2.19/0.99  
% 2.19/0.99  --instantiation_flag                    true
% 2.19/0.99  --inst_sos_flag                         false
% 2.19/0.99  --inst_sos_phase                        true
% 2.19/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.99  --inst_lit_sel_side                     num_symb
% 2.19/0.99  --inst_solver_per_active                1400
% 2.19/0.99  --inst_solver_calls_frac                1.
% 2.19/0.99  --inst_passive_queue_type               priority_queues
% 2.19/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.99  --inst_passive_queues_freq              [25;2]
% 2.19/0.99  --inst_dismatching                      true
% 2.19/0.99  --inst_eager_unprocessed_to_passive     true
% 2.19/0.99  --inst_prop_sim_given                   true
% 2.19/0.99  --inst_prop_sim_new                     false
% 2.19/0.99  --inst_subs_new                         false
% 2.19/0.99  --inst_eq_res_simp                      false
% 2.19/0.99  --inst_subs_given                       false
% 2.19/0.99  --inst_orphan_elimination               true
% 2.19/0.99  --inst_learning_loop_flag               true
% 2.19/0.99  --inst_learning_start                   3000
% 2.19/0.99  --inst_learning_factor                  2
% 2.19/0.99  --inst_start_prop_sim_after_learn       3
% 2.19/0.99  --inst_sel_renew                        solver
% 2.19/0.99  --inst_lit_activity_flag                true
% 2.19/0.99  --inst_restr_to_given                   false
% 2.19/0.99  --inst_activity_threshold               500
% 2.19/0.99  --inst_out_proof                        true
% 2.19/0.99  
% 2.19/0.99  ------ Resolution Options
% 2.19/0.99  
% 2.19/0.99  --resolution_flag                       true
% 2.19/0.99  --res_lit_sel                           adaptive
% 2.19/0.99  --res_lit_sel_side                      none
% 2.19/0.99  --res_ordering                          kbo
% 2.19/0.99  --res_to_prop_solver                    active
% 2.19/0.99  --res_prop_simpl_new                    false
% 2.19/0.99  --res_prop_simpl_given                  true
% 2.19/0.99  --res_passive_queue_type                priority_queues
% 2.19/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.99  --res_passive_queues_freq               [15;5]
% 2.19/0.99  --res_forward_subs                      full
% 2.19/0.99  --res_backward_subs                     full
% 2.19/0.99  --res_forward_subs_resolution           true
% 2.19/0.99  --res_backward_subs_resolution          true
% 2.19/0.99  --res_orphan_elimination                true
% 2.19/0.99  --res_time_limit                        2.
% 2.19/0.99  --res_out_proof                         true
% 2.19/0.99  
% 2.19/0.99  ------ Superposition Options
% 2.19/0.99  
% 2.19/0.99  --superposition_flag                    true
% 2.19/0.99  --sup_passive_queue_type                priority_queues
% 2.19/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.99  --demod_completeness_check              fast
% 2.19/0.99  --demod_use_ground                      true
% 2.19/0.99  --sup_to_prop_solver                    passive
% 2.19/0.99  --sup_prop_simpl_new                    true
% 2.19/0.99  --sup_prop_simpl_given                  true
% 2.19/0.99  --sup_fun_splitting                     false
% 2.19/0.99  --sup_smt_interval                      50000
% 2.19/0.99  
% 2.19/0.99  ------ Superposition Simplification Setup
% 2.19/0.99  
% 2.19/0.99  --sup_indices_passive                   []
% 2.19/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.99  --sup_full_bw                           [BwDemod]
% 2.19/0.99  --sup_immed_triv                        [TrivRules]
% 2.19/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.99  --sup_immed_bw_main                     []
% 2.19/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.99  
% 2.19/0.99  ------ Combination Options
% 2.19/0.99  
% 2.19/0.99  --comb_res_mult                         3
% 2.19/0.99  --comb_sup_mult                         2
% 2.19/0.99  --comb_inst_mult                        10
% 2.19/0.99  
% 2.19/0.99  ------ Debug Options
% 2.19/0.99  
% 2.19/0.99  --dbg_backtrace                         false
% 2.19/0.99  --dbg_dump_prop_clauses                 false
% 2.19/0.99  --dbg_dump_prop_clauses_file            -
% 2.19/0.99  --dbg_out_stat                          false
% 2.19/0.99  ------ Parsing...
% 2.19/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/0.99  
% 2.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.19/0.99  
% 2.19/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/0.99  
% 2.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/0.99  ------ Proving...
% 2.19/0.99  ------ Problem Properties 
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  clauses                                 12
% 2.19/0.99  conjectures                             2
% 2.19/0.99  EPR                                     2
% 2.19/0.99  Horn                                    10
% 2.19/0.99  unary                                   4
% 2.19/0.99  binary                                  2
% 2.19/0.99  lits                                    43
% 2.19/0.99  lits eq                                 6
% 2.19/0.99  fd_pure                                 0
% 2.19/0.99  fd_pseudo                               0
% 2.19/0.99  fd_cond                                 0
% 2.19/0.99  fd_pseudo_cond                          3
% 2.19/0.99  AC symbols                              0
% 2.19/0.99  
% 2.19/0.99  ------ Schedule dynamic 5 is on 
% 2.19/0.99  
% 2.19/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  ------ 
% 2.19/0.99  Current options:
% 2.19/0.99  ------ 
% 2.19/0.99  
% 2.19/0.99  ------ Input Options
% 2.19/0.99  
% 2.19/0.99  --out_options                           all
% 2.19/0.99  --tptp_safe_out                         true
% 2.19/0.99  --problem_path                          ""
% 2.19/0.99  --include_path                          ""
% 2.19/0.99  --clausifier                            res/vclausify_rel
% 2.19/0.99  --clausifier_options                    --mode clausify
% 2.19/0.99  --stdin                                 false
% 2.19/0.99  --stats_out                             all
% 2.19/0.99  
% 2.19/0.99  ------ General Options
% 2.19/0.99  
% 2.19/0.99  --fof                                   false
% 2.19/0.99  --time_out_real                         305.
% 2.19/0.99  --time_out_virtual                      -1.
% 2.19/0.99  --symbol_type_check                     false
% 2.19/0.99  --clausify_out                          false
% 2.19/0.99  --sig_cnt_out                           false
% 2.19/0.99  --trig_cnt_out                          false
% 2.19/0.99  --trig_cnt_out_tolerance                1.
% 2.19/0.99  --trig_cnt_out_sk_spl                   false
% 2.19/0.99  --abstr_cl_out                          false
% 2.19/0.99  
% 2.19/0.99  ------ Global Options
% 2.19/0.99  
% 2.19/0.99  --schedule                              default
% 2.19/0.99  --add_important_lit                     false
% 2.19/0.99  --prop_solver_per_cl                    1000
% 2.19/0.99  --min_unsat_core                        false
% 2.19/0.99  --soft_assumptions                      false
% 2.19/0.99  --soft_lemma_size                       3
% 2.19/0.99  --prop_impl_unit_size                   0
% 2.19/0.99  --prop_impl_unit                        []
% 2.19/0.99  --share_sel_clauses                     true
% 2.19/0.99  --reset_solvers                         false
% 2.19/0.99  --bc_imp_inh                            [conj_cone]
% 2.19/0.99  --conj_cone_tolerance                   3.
% 2.19/0.99  --extra_neg_conj                        none
% 2.19/0.99  --large_theory_mode                     true
% 2.19/0.99  --prolific_symb_bound                   200
% 2.19/0.99  --lt_threshold                          2000
% 2.19/0.99  --clause_weak_htbl                      true
% 2.19/0.99  --gc_record_bc_elim                     false
% 2.19/0.99  
% 2.19/0.99  ------ Preprocessing Options
% 2.19/0.99  
% 2.19/0.99  --preprocessing_flag                    true
% 2.19/0.99  --time_out_prep_mult                    0.1
% 2.19/0.99  --splitting_mode                        input
% 2.19/0.99  --splitting_grd                         true
% 2.19/0.99  --splitting_cvd                         false
% 2.19/0.99  --splitting_cvd_svl                     false
% 2.19/0.99  --splitting_nvd                         32
% 2.19/0.99  --sub_typing                            true
% 2.19/0.99  --prep_gs_sim                           true
% 2.19/0.99  --prep_unflatten                        true
% 2.19/0.99  --prep_res_sim                          true
% 2.19/0.99  --prep_upred                            true
% 2.19/0.99  --prep_sem_filter                       exhaustive
% 2.19/0.99  --prep_sem_filter_out                   false
% 2.19/0.99  --pred_elim                             true
% 2.19/0.99  --res_sim_input                         true
% 2.19/0.99  --eq_ax_congr_red                       true
% 2.19/0.99  --pure_diseq_elim                       true
% 2.19/0.99  --brand_transform                       false
% 2.19/0.99  --non_eq_to_eq                          false
% 2.19/0.99  --prep_def_merge                        true
% 2.19/0.99  --prep_def_merge_prop_impl              false
% 2.19/0.99  --prep_def_merge_mbd                    true
% 2.19/0.99  --prep_def_merge_tr_red                 false
% 2.19/0.99  --prep_def_merge_tr_cl                  false
% 2.19/0.99  --smt_preprocessing                     true
% 2.19/0.99  --smt_ac_axioms                         fast
% 2.19/0.99  --preprocessed_out                      false
% 2.19/0.99  --preprocessed_stats                    false
% 2.19/0.99  
% 2.19/0.99  ------ Abstraction refinement Options
% 2.19/0.99  
% 2.19/0.99  --abstr_ref                             []
% 2.19/0.99  --abstr_ref_prep                        false
% 2.19/0.99  --abstr_ref_until_sat                   false
% 2.19/0.99  --abstr_ref_sig_restrict                funpre
% 2.19/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.99  --abstr_ref_under                       []
% 2.19/0.99  
% 2.19/0.99  ------ SAT Options
% 2.19/0.99  
% 2.19/0.99  --sat_mode                              false
% 2.19/0.99  --sat_fm_restart_options                ""
% 2.19/0.99  --sat_gr_def                            false
% 2.19/0.99  --sat_epr_types                         true
% 2.19/0.99  --sat_non_cyclic_types                  false
% 2.19/0.99  --sat_finite_models                     false
% 2.19/0.99  --sat_fm_lemmas                         false
% 2.19/0.99  --sat_fm_prep                           false
% 2.19/0.99  --sat_fm_uc_incr                        true
% 2.19/0.99  --sat_out_model                         small
% 2.19/0.99  --sat_out_clauses                       false
% 2.19/0.99  
% 2.19/0.99  ------ QBF Options
% 2.19/0.99  
% 2.19/0.99  --qbf_mode                              false
% 2.19/0.99  --qbf_elim_univ                         false
% 2.19/0.99  --qbf_dom_inst                          none
% 2.19/0.99  --qbf_dom_pre_inst                      false
% 2.19/0.99  --qbf_sk_in                             false
% 2.19/0.99  --qbf_pred_elim                         true
% 2.19/0.99  --qbf_split                             512
% 2.19/0.99  
% 2.19/0.99  ------ BMC1 Options
% 2.19/0.99  
% 2.19/0.99  --bmc1_incremental                      false
% 2.19/0.99  --bmc1_axioms                           reachable_all
% 2.19/0.99  --bmc1_min_bound                        0
% 2.19/0.99  --bmc1_max_bound                        -1
% 2.19/0.99  --bmc1_max_bound_default                -1
% 2.19/0.99  --bmc1_symbol_reachability              true
% 2.19/0.99  --bmc1_property_lemmas                  false
% 2.19/0.99  --bmc1_k_induction                      false
% 2.19/0.99  --bmc1_non_equiv_states                 false
% 2.19/0.99  --bmc1_deadlock                         false
% 2.19/0.99  --bmc1_ucm                              false
% 2.19/0.99  --bmc1_add_unsat_core                   none
% 2.19/0.99  --bmc1_unsat_core_children              false
% 2.19/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.99  --bmc1_out_stat                         full
% 2.19/0.99  --bmc1_ground_init                      false
% 2.19/0.99  --bmc1_pre_inst_next_state              false
% 2.19/0.99  --bmc1_pre_inst_state                   false
% 2.19/0.99  --bmc1_pre_inst_reach_state             false
% 2.19/0.99  --bmc1_out_unsat_core                   false
% 2.19/0.99  --bmc1_aig_witness_out                  false
% 2.19/0.99  --bmc1_verbose                          false
% 2.19/0.99  --bmc1_dump_clauses_tptp                false
% 2.19/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.99  --bmc1_dump_file                        -
% 2.19/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.99  --bmc1_ucm_extend_mode                  1
% 2.19/0.99  --bmc1_ucm_init_mode                    2
% 2.19/0.99  --bmc1_ucm_cone_mode                    none
% 2.19/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.99  --bmc1_ucm_relax_model                  4
% 2.19/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.99  --bmc1_ucm_layered_model                none
% 2.19/0.99  --bmc1_ucm_max_lemma_size               10
% 2.19/0.99  
% 2.19/0.99  ------ AIG Options
% 2.19/0.99  
% 2.19/0.99  --aig_mode                              false
% 2.19/0.99  
% 2.19/0.99  ------ Instantiation Options
% 2.19/0.99  
% 2.19/0.99  --instantiation_flag                    true
% 2.19/0.99  --inst_sos_flag                         false
% 2.19/0.99  --inst_sos_phase                        true
% 2.19/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.99  --inst_lit_sel_side                     none
% 2.19/0.99  --inst_solver_per_active                1400
% 2.19/0.99  --inst_solver_calls_frac                1.
% 2.19/0.99  --inst_passive_queue_type               priority_queues
% 2.19/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.99  --inst_passive_queues_freq              [25;2]
% 2.19/0.99  --inst_dismatching                      true
% 2.19/0.99  --inst_eager_unprocessed_to_passive     true
% 2.19/0.99  --inst_prop_sim_given                   true
% 2.19/0.99  --inst_prop_sim_new                     false
% 2.19/0.99  --inst_subs_new                         false
% 2.19/0.99  --inst_eq_res_simp                      false
% 2.19/0.99  --inst_subs_given                       false
% 2.19/0.99  --inst_orphan_elimination               true
% 2.19/0.99  --inst_learning_loop_flag               true
% 2.19/0.99  --inst_learning_start                   3000
% 2.19/0.99  --inst_learning_factor                  2
% 2.19/0.99  --inst_start_prop_sim_after_learn       3
% 2.19/0.99  --inst_sel_renew                        solver
% 2.19/0.99  --inst_lit_activity_flag                true
% 2.19/0.99  --inst_restr_to_given                   false
% 2.19/0.99  --inst_activity_threshold               500
% 2.19/0.99  --inst_out_proof                        true
% 2.19/0.99  
% 2.19/0.99  ------ Resolution Options
% 2.19/0.99  
% 2.19/0.99  --resolution_flag                       false
% 2.19/0.99  --res_lit_sel                           adaptive
% 2.19/0.99  --res_lit_sel_side                      none
% 2.19/0.99  --res_ordering                          kbo
% 2.19/0.99  --res_to_prop_solver                    active
% 2.19/0.99  --res_prop_simpl_new                    false
% 2.19/0.99  --res_prop_simpl_given                  true
% 2.19/0.99  --res_passive_queue_type                priority_queues
% 2.19/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.99  --res_passive_queues_freq               [15;5]
% 2.19/0.99  --res_forward_subs                      full
% 2.19/0.99  --res_backward_subs                     full
% 2.19/0.99  --res_forward_subs_resolution           true
% 2.19/0.99  --res_backward_subs_resolution          true
% 2.19/0.99  --res_orphan_elimination                true
% 2.19/0.99  --res_time_limit                        2.
% 2.19/0.99  --res_out_proof                         true
% 2.19/0.99  
% 2.19/0.99  ------ Superposition Options
% 2.19/0.99  
% 2.19/0.99  --superposition_flag                    true
% 2.19/0.99  --sup_passive_queue_type                priority_queues
% 2.19/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.99  --demod_completeness_check              fast
% 2.19/0.99  --demod_use_ground                      true
% 2.19/0.99  --sup_to_prop_solver                    passive
% 2.19/0.99  --sup_prop_simpl_new                    true
% 2.19/0.99  --sup_prop_simpl_given                  true
% 2.19/0.99  --sup_fun_splitting                     false
% 2.19/0.99  --sup_smt_interval                      50000
% 2.19/0.99  
% 2.19/0.99  ------ Superposition Simplification Setup
% 2.19/0.99  
% 2.19/0.99  --sup_indices_passive                   []
% 2.19/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.99  --sup_full_bw                           [BwDemod]
% 2.19/0.99  --sup_immed_triv                        [TrivRules]
% 2.19/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.99  --sup_immed_bw_main                     []
% 2.19/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.99  
% 2.19/0.99  ------ Combination Options
% 2.19/0.99  
% 2.19/0.99  --comb_res_mult                         3
% 2.19/0.99  --comb_sup_mult                         2
% 2.19/0.99  --comb_inst_mult                        10
% 2.19/0.99  
% 2.19/0.99  ------ Debug Options
% 2.19/0.99  
% 2.19/0.99  --dbg_backtrace                         false
% 2.19/0.99  --dbg_dump_prop_clauses                 false
% 2.19/0.99  --dbg_dump_prop_clauses_file            -
% 2.19/0.99  --dbg_out_stat                          false
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  ------ Proving...
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  % SZS status Theorem for theBenchmark.p
% 2.19/0.99  
% 2.19/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/0.99  
% 2.19/0.99  fof(f7,conjecture,(
% 2.19/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.19/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.99  
% 2.19/0.99  fof(f8,negated_conjecture,(
% 2.19/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.19/0.99    inference(negated_conjecture,[],[f7])).
% 2.19/0.99  
% 2.19/0.99  fof(f13,plain,(
% 2.19/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 2.19/0.99    inference(ennf_transformation,[],[f8])).
% 2.19/0.99  
% 2.19/0.99  fof(f22,plain,(
% 2.19/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)) & v1_relat_1(sK5))),
% 2.19/0.99    introduced(choice_axiom,[])).
% 2.19/0.99  
% 2.19/0.99  fof(f23,plain,(
% 2.19/0.99    (k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)) & v1_relat_1(sK5)),
% 2.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f22])).
% 2.19/0.99  
% 2.19/0.99  fof(f36,plain,(
% 2.19/0.99    v1_relat_1(sK5)),
% 2.19/0.99    inference(cnf_transformation,[],[f23])).
% 2.19/0.99  
% 2.19/0.99  fof(f6,axiom,(
% 2.19/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 2.19/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.99  
% 2.19/0.99  fof(f12,plain,(
% 2.19/0.99    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.19/0.99    inference(ennf_transformation,[],[f6])).
% 2.19/0.99  
% 2.19/0.99  fof(f16,plain,(
% 2.19/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.19/0.99    inference(nnf_transformation,[],[f12])).
% 2.19/0.99  
% 2.19/0.99  fof(f17,plain,(
% 2.19/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.19/0.99    inference(rectify,[],[f16])).
% 2.19/0.99  
% 2.19/0.99  fof(f20,plain,(
% 2.19/0.99    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)))),
% 2.19/0.99    introduced(choice_axiom,[])).
% 2.19/0.99  
% 2.19/0.99  fof(f19,plain,(
% 2.19/0.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0)))) )),
% 2.19/0.99    introduced(choice_axiom,[])).
% 2.19/0.99  
% 2.19/0.99  fof(f18,plain,(
% 2.19/0.99    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 2.19/0.99    introduced(choice_axiom,[])).
% 2.19/0.99  
% 2.19/0.99  fof(f21,plain,(
% 2.19/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f20,f19,f18])).
% 2.19/0.99  
% 2.19/0.99  fof(f33,plain,(
% 2.19/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.19/0.99    inference(cnf_transformation,[],[f21])).
% 2.19/0.99  
% 2.19/0.99  fof(f2,axiom,(
% 2.19/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.99  
% 2.19/0.99  fof(f9,plain,(
% 2.19/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.99    inference(rectify,[],[f2])).
% 2.19/0.99  
% 2.19/0.99  fof(f10,plain,(
% 2.19/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.19/0.99    inference(ennf_transformation,[],[f9])).
% 2.19/0.99  
% 2.19/0.99  fof(f14,plain,(
% 2.19/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.19/0.99    introduced(choice_axiom,[])).
% 2.19/0.99  
% 2.19/0.99  fof(f15,plain,(
% 2.19/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 2.19/0.99  
% 2.19/0.99  fof(f26,plain,(
% 2.19/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.19/0.99    inference(cnf_transformation,[],[f15])).
% 2.19/0.99  
% 2.19/0.99  fof(f4,axiom,(
% 2.19/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.19/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.99  
% 2.19/0.99  fof(f28,plain,(
% 2.19/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.19/0.99    inference(cnf_transformation,[],[f4])).
% 2.19/0.99  
% 2.19/0.99  fof(f3,axiom,(
% 2.19/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.19/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.99  
% 2.19/0.99  fof(f27,plain,(
% 2.19/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.19/0.99    inference(cnf_transformation,[],[f3])).
% 2.19/0.99  
% 2.19/0.99  fof(f5,axiom,(
% 2.19/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.19/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.99  
% 2.19/0.99  fof(f11,plain,(
% 2.19/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.19/0.99    inference(ennf_transformation,[],[f5])).
% 2.19/0.99  
% 2.19/0.99  fof(f29,plain,(
% 2.19/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.19/0.99    inference(cnf_transformation,[],[f11])).
% 2.19/0.99  
% 2.19/0.99  fof(f1,axiom,(
% 2.19/0.99    v1_xboole_0(k1_xboole_0)),
% 2.19/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.99  
% 2.19/0.99  fof(f24,plain,(
% 2.19/0.99    v1_xboole_0(k1_xboole_0)),
% 2.19/0.99    inference(cnf_transformation,[],[f1])).
% 2.19/0.99  
% 2.19/0.99  fof(f34,plain,(
% 2.19/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.19/0.99    inference(cnf_transformation,[],[f21])).
% 2.19/0.99  
% 2.19/0.99  fof(f37,plain,(
% 2.19/0.99    k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5)),
% 2.19/0.99    inference(cnf_transformation,[],[f23])).
% 2.19/0.99  
% 2.19/0.99  cnf(c_13,negated_conjecture,
% 2.19/0.99      ( v1_relat_1(sK5) ),
% 2.19/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_249,negated_conjecture,
% 2.19/0.99      ( v1_relat_1(sK5) ),
% 2.19/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_468,plain,
% 2.19/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_8,plain,
% 2.19/0.99      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
% 2.19/0.99      | ~ v1_relat_1(X2)
% 2.19/0.99      | ~ v1_relat_1(X1)
% 2.19/0.99      | ~ v1_relat_1(X0)
% 2.19/0.99      | k5_relat_1(X0,X1) = X2 ),
% 2.19/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_254,plain,
% 2.19/0.99      ( r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK3(X0_43,X1_43,X2_43)),X0_43)
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43)
% 2.19/0.99      | ~ v1_relat_1(X2_43)
% 2.19/0.99      | ~ v1_relat_1(X1_43)
% 2.19/0.99      | ~ v1_relat_1(X0_43)
% 2.19/0.99      | k5_relat_1(X0_43,X1_43) = X2_43 ),
% 2.19/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_464,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,X1_43) = X2_43
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK3(X0_43,X1_43,X2_43)),X0_43) = iProver_top
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43) = iProver_top
% 2.19/0.99      | v1_relat_1(X2_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 2.19/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_4,plain,
% 2.19/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_163,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 2.19/0.99      | X3 != X1
% 2.19/0.99      | k1_xboole_0 != X2 ),
% 2.19/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_164,plain,
% 2.19/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 2.19/0.99      inference(unflattening,[status(thm)],[c_163]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_246,plain,
% 2.19/0.99      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_44,k1_xboole_0)) ),
% 2.19/0.99      inference(subtyping,[status(esa)],[c_164]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_471,plain,
% 2.19/0.99      ( r2_hidden(X0_42,k3_xboole_0(X0_44,k1_xboole_0)) != iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_3,plain,
% 2.19/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.19/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_257,plain,
% 2.19/0.99      ( k3_xboole_0(X0_44,k1_xboole_0) = k1_xboole_0 ),
% 2.19/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_478,plain,
% 2.19/0.99      ( r2_hidden(X0_42,k1_xboole_0) != iProver_top ),
% 2.19/0.99      inference(light_normalisation,[status(thm)],[c_471,c_257]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1163,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,k1_xboole_0),sK3(X0_43,X1_43,k1_xboole_0)),X0_43) = iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_464,c_478]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_5,plain,
% 2.19/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_33,plain,
% 2.19/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_35,plain,
% 2.19/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 2.19/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.19/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_0,plain,
% 2.19/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.19/0.99      inference(cnf_transformation,[],[f24]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_44,plain,
% 2.19/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_4034,plain,
% 2.19/0.99      ( v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,k1_xboole_0),sK3(X0_43,X1_43,k1_xboole_0)),X0_43) = iProver_top
% 2.19/0.99      | k5_relat_1(X0_43,X1_43) = k1_xboole_0 ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_1163,c_35,c_44]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_4035,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,k1_xboole_0),sK3(X0_43,X1_43,k1_xboole_0)),X0_43) = iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 2.19/0.99      inference(renaming,[status(thm)],[c_4034]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_4044,plain,
% 2.19/0.99      ( k5_relat_1(k1_xboole_0,X0_43) = k1_xboole_0
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_4035,c_478]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_4233,plain,
% 2.19/0.99      ( v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | k5_relat_1(k1_xboole_0,X0_43) = k1_xboole_0 ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_4044,c_35,c_44]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_4234,plain,
% 2.19/0.99      ( k5_relat_1(k1_xboole_0,X0_43) = k1_xboole_0
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 2.19/0.99      inference(renaming,[status(thm)],[c_4233]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_4239,plain,
% 2.19/0.99      ( k5_relat_1(k1_xboole_0,sK5) = k1_xboole_0 ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_468,c_4234]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_7,plain,
% 2.19/0.99      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
% 2.19/0.99      | ~ v1_relat_1(X2)
% 2.19/0.99      | ~ v1_relat_1(X1)
% 2.19/0.99      | ~ v1_relat_1(X0)
% 2.19/0.99      | k5_relat_1(X0,X1) = X2 ),
% 2.19/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_255,plain,
% 2.19/0.99      ( r2_hidden(k4_tarski(sK3(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X1_43)
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43)
% 2.19/0.99      | ~ v1_relat_1(X2_43)
% 2.19/0.99      | ~ v1_relat_1(X1_43)
% 2.19/0.99      | ~ v1_relat_1(X0_43)
% 2.19/0.99      | k5_relat_1(X0_43,X1_43) = X2_43 ),
% 2.19/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_463,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,X1_43) = X2_43
% 2.19/0.99      | r2_hidden(k4_tarski(sK3(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X1_43) = iProver_top
% 2.19/0.99      | r2_hidden(k4_tarski(sK1(X0_43,X1_43,X2_43),sK2(X0_43,X1_43,X2_43)),X2_43) = iProver_top
% 2.19/0.99      | v1_relat_1(X2_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 2.19/0.99      inference(predicate_to_equality,[status(thm)],[c_255]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_970,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
% 2.19/0.99      | r2_hidden(k4_tarski(sK3(X0_43,X1_43,k1_xboole_0),sK2(X0_43,X1_43,k1_xboole_0)),X1_43) = iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_463,c_478]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2678,plain,
% 2.19/0.99      ( v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | r2_hidden(k4_tarski(sK3(X0_43,X1_43,k1_xboole_0),sK2(X0_43,X1_43,k1_xboole_0)),X1_43) = iProver_top
% 2.19/0.99      | k5_relat_1(X0_43,X1_43) = k1_xboole_0 ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_970,c_35,c_44]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2679,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,X1_43) = k1_xboole_0
% 2.19/0.99      | r2_hidden(k4_tarski(sK3(X0_43,X1_43,k1_xboole_0),sK2(X0_43,X1_43,k1_xboole_0)),X1_43) = iProver_top
% 2.19/0.99      | v1_relat_1(X1_43) != iProver_top
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 2.19/0.99      inference(renaming,[status(thm)],[c_2678]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2688,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,k1_xboole_0) = k1_xboole_0
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_2679,c_478]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2861,plain,
% 2.19/0.99      ( v1_relat_1(X0_43) != iProver_top
% 2.19/0.99      | k5_relat_1(X0_43,k1_xboole_0) = k1_xboole_0 ),
% 2.19/0.99      inference(global_propositional_subsumption,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_2688,c_35,c_44]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2862,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,k1_xboole_0) = k1_xboole_0
% 2.19/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 2.19/0.99      inference(renaming,[status(thm)],[c_2861]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_2867,plain,
% 2.19/0.99      ( k5_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 2.19/0.99      inference(superposition,[status(thm)],[c_468,c_2862]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_262,plain,
% 2.19/0.99      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 2.19/0.99      theory(equality) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_681,plain,
% 2.19/0.99      ( k5_relat_1(X0_43,X1_43) != X2_43
% 2.19/0.99      | k1_xboole_0 != X2_43
% 2.19/0.99      | k1_xboole_0 = k5_relat_1(X0_43,X1_43) ),
% 2.19/0.99      inference(instantiation,[status(thm)],[c_262]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1668,plain,
% 2.19/0.99      ( k5_relat_1(k1_xboole_0,sK5) != X0_43
% 2.19/0.99      | k1_xboole_0 != X0_43
% 2.19/0.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK5) ),
% 2.19/0.99      inference(instantiation,[status(thm)],[c_681]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_1669,plain,
% 2.19/0.99      ( k5_relat_1(k1_xboole_0,sK5) != k1_xboole_0
% 2.19/0.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK5)
% 2.19/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.19/0.99      inference(instantiation,[status(thm)],[c_1668]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_583,plain,
% 2.19/0.99      ( k5_relat_1(sK5,k1_xboole_0) != X0_43
% 2.19/0.99      | k1_xboole_0 != X0_43
% 2.19/0.99      | k1_xboole_0 = k5_relat_1(sK5,k1_xboole_0) ),
% 2.19/0.99      inference(instantiation,[status(thm)],[c_262]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_584,plain,
% 2.19/0.99      ( k5_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 2.19/0.99      | k1_xboole_0 = k5_relat_1(sK5,k1_xboole_0)
% 2.19/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.19/0.99      inference(instantiation,[status(thm)],[c_583]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_12,negated_conjecture,
% 2.19/0.99      ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
% 2.19/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
% 2.19/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_250,negated_conjecture,
% 2.19/0.99      ( k1_xboole_0 != k5_relat_1(sK5,k1_xboole_0)
% 2.19/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK5) ),
% 2.19/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_260,plain,( X0_43 = X0_43 ),theory(equality) ).
% 2.19/0.99  
% 2.19/0.99  cnf(c_275,plain,
% 2.19/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.19/0.99      inference(instantiation,[status(thm)],[c_260]) ).
% 2.19/0.99  
% 2.19/0.99  cnf(contradiction,plain,
% 2.19/0.99      ( $false ),
% 2.19/0.99      inference(minisat,
% 2.19/0.99                [status(thm)],
% 2.19/0.99                [c_4239,c_2867,c_1669,c_584,c_250,c_275]) ).
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/0.99  
% 2.19/0.99  ------                               Statistics
% 2.19/0.99  
% 2.19/0.99  ------ General
% 2.19/0.99  
% 2.19/0.99  abstr_ref_over_cycles:                  0
% 2.19/0.99  abstr_ref_under_cycles:                 0
% 2.19/0.99  gc_basic_clause_elim:                   0
% 2.19/0.99  forced_gc_time:                         0
% 2.19/0.99  parsing_time:                           0.005
% 2.19/0.99  unif_index_cands_time:                  0.
% 2.19/0.99  unif_index_add_time:                    0.
% 2.19/0.99  orderings_time:                         0.
% 2.19/0.99  out_proof_time:                         0.015
% 2.19/0.99  total_time:                             0.124
% 2.19/0.99  num_of_symbols:                         49
% 2.19/0.99  num_of_terms:                           3944
% 2.19/0.99  
% 2.19/0.99  ------ Preprocessing
% 2.19/0.99  
% 2.19/0.99  num_of_splits:                          0
% 2.19/0.99  num_of_split_atoms:                     0
% 2.19/0.99  num_of_reused_defs:                     0
% 2.19/0.99  num_eq_ax_congr_red:                    49
% 2.19/0.99  num_of_sem_filtered_clauses:            1
% 2.19/0.99  num_of_subtypes:                        4
% 2.19/0.99  monotx_restored_types:                  0
% 2.19/0.99  sat_num_of_epr_types:                   0
% 2.19/0.99  sat_num_of_non_cyclic_types:            0
% 2.19/0.99  sat_guarded_non_collapsed_types:        1
% 2.19/0.99  num_pure_diseq_elim:                    0
% 2.19/0.99  simp_replaced_by:                       0
% 2.19/0.99  res_preprocessed:                       69
% 2.19/0.99  prep_upred:                             0
% 2.19/0.99  prep_unflattend:                        5
% 2.19/0.99  smt_new_axioms:                         0
% 2.19/0.99  pred_elim_cands:                        2
% 2.19/0.99  pred_elim:                              2
% 2.19/0.99  pred_elim_cl:                           2
% 2.19/0.99  pred_elim_cycles:                       4
% 2.19/0.99  merged_defs:                            0
% 2.19/0.99  merged_defs_ncl:                        0
% 2.19/0.99  bin_hyper_res:                          0
% 2.19/0.99  prep_cycles:                            4
% 2.19/0.99  pred_elim_time:                         0.
% 2.19/0.99  splitting_time:                         0.
% 2.19/0.99  sem_filter_time:                        0.
% 2.19/0.99  monotx_time:                            0.
% 2.19/0.99  subtype_inf_time:                       0.
% 2.19/0.99  
% 2.19/0.99  ------ Problem properties
% 2.19/0.99  
% 2.19/0.99  clauses:                                12
% 2.19/0.99  conjectures:                            2
% 2.19/0.99  epr:                                    2
% 2.19/0.99  horn:                                   10
% 2.19/0.99  ground:                                 3
% 2.19/0.99  unary:                                  4
% 2.19/0.99  binary:                                 2
% 2.19/0.99  lits:                                   43
% 2.19/0.99  lits_eq:                                6
% 2.19/0.99  fd_pure:                                0
% 2.19/0.99  fd_pseudo:                              0
% 2.19/0.99  fd_cond:                                0
% 2.19/0.99  fd_pseudo_cond:                         3
% 2.19/0.99  ac_symbols:                             0
% 2.19/0.99  
% 2.19/0.99  ------ Propositional Solver
% 2.19/0.99  
% 2.19/0.99  prop_solver_calls:                      29
% 2.19/0.99  prop_fast_solver_calls:                 631
% 2.19/0.99  smt_solver_calls:                       0
% 2.19/0.99  smt_fast_solver_calls:                  0
% 2.19/0.99  prop_num_of_clauses:                    987
% 2.19/0.99  prop_preprocess_simplified:             2529
% 2.19/0.99  prop_fo_subsumed:                       7
% 2.19/0.99  prop_solver_time:                       0.
% 2.19/0.99  smt_solver_time:                        0.
% 2.19/0.99  smt_fast_solver_time:                   0.
% 2.19/0.99  prop_fast_solver_time:                  0.
% 2.19/0.99  prop_unsat_core_time:                   0.
% 2.19/0.99  
% 2.19/0.99  ------ QBF
% 2.19/0.99  
% 2.19/0.99  qbf_q_res:                              0
% 2.19/0.99  qbf_num_tautologies:                    0
% 2.19/0.99  qbf_prep_cycles:                        0
% 2.19/0.99  
% 2.19/0.99  ------ BMC1
% 2.19/0.99  
% 2.19/0.99  bmc1_current_bound:                     -1
% 2.19/0.99  bmc1_last_solved_bound:                 -1
% 2.19/0.99  bmc1_unsat_core_size:                   -1
% 2.19/0.99  bmc1_unsat_core_parents_size:           -1
% 2.19/0.99  bmc1_merge_next_fun:                    0
% 2.19/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.19/0.99  
% 2.19/0.99  ------ Instantiation
% 2.19/0.99  
% 2.19/0.99  inst_num_of_clauses:                    225
% 2.19/0.99  inst_num_in_passive:                    29
% 2.19/0.99  inst_num_in_active:                     153
% 2.19/0.99  inst_num_in_unprocessed:                43
% 2.19/0.99  inst_num_of_loops:                      190
% 2.19/0.99  inst_num_of_learning_restarts:          0
% 2.19/0.99  inst_num_moves_active_passive:          33
% 2.19/0.99  inst_lit_activity:                      0
% 2.19/0.99  inst_lit_activity_moves:                0
% 2.19/0.99  inst_num_tautologies:                   0
% 2.19/0.99  inst_num_prop_implied:                  0
% 2.19/0.99  inst_num_existing_simplified:           0
% 2.19/0.99  inst_num_eq_res_simplified:             0
% 2.19/0.99  inst_num_child_elim:                    0
% 2.19/0.99  inst_num_of_dismatching_blockings:      117
% 2.19/0.99  inst_num_of_non_proper_insts:           274
% 2.19/0.99  inst_num_of_duplicates:                 0
% 2.19/0.99  inst_inst_num_from_inst_to_res:         0
% 2.19/0.99  inst_dismatching_checking_time:         0.
% 2.19/0.99  
% 2.19/0.99  ------ Resolution
% 2.19/0.99  
% 2.19/0.99  res_num_of_clauses:                     0
% 2.19/0.99  res_num_in_passive:                     0
% 2.19/0.99  res_num_in_active:                      0
% 2.19/0.99  res_num_of_loops:                       73
% 2.19/0.99  res_forward_subset_subsumed:            32
% 2.19/0.99  res_backward_subset_subsumed:           0
% 2.19/0.99  res_forward_subsumed:                   0
% 2.19/0.99  res_backward_subsumed:                  0
% 2.19/0.99  res_forward_subsumption_resolution:     0
% 2.19/0.99  res_backward_subsumption_resolution:    0
% 2.19/0.99  res_clause_to_clause_subsumption:       435
% 2.19/0.99  res_orphan_elimination:                 0
% 2.19/0.99  res_tautology_del:                      28
% 2.19/0.99  res_num_eq_res_simplified:              0
% 2.19/0.99  res_num_sel_changes:                    0
% 2.19/0.99  res_moves_from_active_to_pass:          0
% 2.19/0.99  
% 2.19/0.99  ------ Superposition
% 2.19/0.99  
% 2.19/0.99  sup_time_total:                         0.
% 2.19/0.99  sup_time_generating:                    0.
% 2.19/0.99  sup_time_sim_full:                      0.
% 2.19/0.99  sup_time_sim_immed:                     0.
% 2.19/0.99  
% 2.19/0.99  sup_num_of_clauses:                     136
% 2.19/0.99  sup_num_in_active:                      37
% 2.19/0.99  sup_num_in_passive:                     99
% 2.19/0.99  sup_num_of_loops:                       37
% 2.19/0.99  sup_fw_superposition:                   80
% 2.19/0.99  sup_bw_superposition:                   85
% 2.19/0.99  sup_immediate_simplified:               32
% 2.19/0.99  sup_given_eliminated:                   0
% 2.19/0.99  comparisons_done:                       0
% 2.19/0.99  comparisons_avoided:                    0
% 2.19/0.99  
% 2.19/0.99  ------ Simplifications
% 2.19/0.99  
% 2.19/0.99  
% 2.19/0.99  sim_fw_subset_subsumed:                 1
% 2.19/0.99  sim_bw_subset_subsumed:                 0
% 2.19/0.99  sim_fw_subsumed:                        28
% 2.19/0.99  sim_bw_subsumed:                        0
% 2.19/0.99  sim_fw_subsumption_res:                 0
% 2.19/0.99  sim_bw_subsumption_res:                 0
% 2.19/0.99  sim_tautology_del:                      1
% 2.19/0.99  sim_eq_tautology_del:                   0
% 2.19/0.99  sim_eq_res_simp:                        1
% 2.19/0.99  sim_fw_demodulated:                     0
% 2.19/0.99  sim_bw_demodulated:                     1
% 2.19/0.99  sim_light_normalised:                   21
% 2.19/0.99  sim_joinable_taut:                      0
% 2.19/0.99  sim_joinable_simp:                      0
% 2.19/0.99  sim_ac_normalised:                      0
% 2.19/0.99  sim_smt_subsumption:                    0
% 2.19/0.99  
%------------------------------------------------------------------------------
