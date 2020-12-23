%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0825+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:11 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 116 expanded)
%              Number of clauses        :   38 (  45 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   15
%              Number of atoms          :  244 ( 426 expanded)
%              Number of equality atoms :   79 ( 111 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f24,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f5,conjecture,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,
    ( ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ~ r1_tarski(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f21])).

fof(f36,plain,(
    ~ r1_tarski(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f23,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_326,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_7])).

cnf(c_327,plain,
    ( r1_tarski(k6_relat_1(X0),X1)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_831,plain,
    ( r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_297,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | X1 = X0
    | k6_relat_1(X2) != k6_relat_1(X3) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_4])).

cnf(c_833,plain,
    ( X0 = X1
    | k6_relat_1(X2) != k6_relat_1(X3)
    | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_962,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_833])).

cnf(c_1275,plain,
    ( sK3(k6_relat_1(X0),X1) = sK2(k6_relat_1(X0),X1)
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_962])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_839,plain,
    ( r1_tarski(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2452,plain,
    ( sK3(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) = sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_1275,c_839])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_338,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_6])).

cnf(c_339,plain,
    ( r1_tarski(k6_relat_1(X0),X1)
    | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_830,plain,
    ( r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK3(k6_relat_1(X0),X1)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_2467,plain,
    ( r1_tarski(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k2_zfmisc_1(sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_830])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1059,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK4)
    | r2_hidden(k4_tarski(X0,sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k2_zfmisc_1(X1,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1250,plain,
    ( ~ r2_hidden(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK4)
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k2_zfmisc_1(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_1251,plain,
    ( r2_hidden(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k2_zfmisc_1(sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_269,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | k6_relat_1(X1) != k6_relat_1(X3) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_5])).

cnf(c_979,plain,
    ( r2_hidden(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK4)
    | ~ r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK3(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k6_relat_1(sK4))
    | k6_relat_1(sK4) != k6_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_980,plain,
    ( k6_relat_1(sK4) != k6_relat_1(X0)
    | r2_hidden(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK4) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK3(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k6_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_982,plain,
    ( k6_relat_1(sK4) != k6_relat_1(sK4)
    | r2_hidden(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK4) = iProver_top
    | r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK3(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k6_relat_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_592,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_613,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_594,plain,
    ( X0 != X1
    | k6_relat_1(X0) = k6_relat_1(X1) ),
    theory(equality)).

cnf(c_603,plain,
    ( k6_relat_1(sK4) = k6_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_189,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | k2_zfmisc_1(sK4,sK4) != X1
    | k6_relat_1(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_190,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK3(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k6_relat_1(sK4))
    | ~ v1_relat_1(k6_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_191,plain,
    ( r2_hidden(k4_tarski(sK2(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)),sK3(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4))),k6_relat_1(sK4)) = iProver_top
    | v1_relat_1(k6_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_22,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_24,plain,
    ( v1_relat_1(k6_relat_1(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( r1_tarski(k6_relat_1(sK4),k2_zfmisc_1(sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2467,c_1251,c_982,c_613,c_603,c_191,c_24,c_14])).


%------------------------------------------------------------------------------
