%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0532+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:30 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 218 expanded)
%              Number of clauses        :   49 (  81 expanded)
%              Number of leaves         :    8 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  353 ( 990 expanded)
%              Number of equality atoms :  106 ( 152 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK1(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                    & r2_hidden(sK1(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f24,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f25,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,sK6))
        & r1_tarski(X1,sK6)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(sK4,sK5),k8_relat_1(sK4,X2))
          & r1_tarski(sK5,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k8_relat_1(sK4,sK5),k8_relat_1(sK4,sK6))
    & r1_tarski(sK5,sK6)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f10,f21,f20])).

fof(f36,plain,(
    ~ r1_tarski(k8_relat_1(sK4,sK5),k8_relat_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_250,plain,
    ( r1_tarski(X0_40,X1_40)
    | r2_hidden(k4_tarski(sK2(X0_40,X1_40),sK3(X0_40,X1_40)),X0_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_539,plain,
    ( r1_tarski(X0_40,X1_40) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0_40,X1_40),sK3(X0_40,X1_40)),X0_40) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_253,plain,
    ( r2_hidden(k4_tarski(X0_42,X0_41),X0_40)
    | ~ r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X1_40,X0_40))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k8_relat_1(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_536,plain,
    ( r2_hidden(k4_tarski(X0_42,X0_41),X0_40) = iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X1_40,X0_40)) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k8_relat_1(X1_40,X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_248,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k8_relat_1(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_541,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k8_relat_1(X1_40,X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_590,plain,
    ( r2_hidden(k4_tarski(X0_42,X0_41),X0_40) = iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X1_40,X0_40)) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_536,c_541])).

cnf(c_949,plain,
    ( r1_tarski(k8_relat_1(X0_40,X1_40),X2_40) = iProver_top
    | r2_hidden(k4_tarski(sK2(k8_relat_1(X0_40,X1_40),X2_40),sK3(k8_relat_1(X0_40,X1_40),X2_40)),X1_40) = iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(k8_relat_1(X0_40,X1_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_590])).

cnf(c_2131,plain,
    ( r1_tarski(k8_relat_1(X0_40,X1_40),X2_40) = iProver_top
    | r2_hidden(k4_tarski(sK2(k8_relat_1(X0_40,X1_40),X2_40),sK3(k8_relat_1(X0_40,X1_40),X2_40)),X1_40) = iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_949,c_541])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X0)
    | r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r2_hidden(k4_tarski(X0_42,X0_41),X0_40)
    | r2_hidden(k4_tarski(X0_42,X0_41),X1_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_540,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),X0_40) != iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),X1_40) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_2135,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(k8_relat_1(X2_40,X0_40),X3_40) = iProver_top
    | r2_hidden(k4_tarski(sK2(k8_relat_1(X2_40,X0_40),X3_40),sK3(k8_relat_1(X2_40,X0_40),X3_40)),X1_40) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_540])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_251,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r2_hidden(k4_tarski(sK2(X0_40,X1_40),sK3(X0_40,X1_40)),X1_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_538,plain,
    ( r1_tarski(X0_40,X1_40) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0_40,X1_40),sK3(X0_40,X1_40)),X1_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_2291,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(k8_relat_1(X2_40,X0_40),X1_40) = iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k8_relat_1(X2_40,X0_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2135,c_538])).

cnf(c_2527,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(k8_relat_1(X2_40,X0_40),X1_40) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2291,c_541])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_252,plain,
    ( r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X0_40,X1_40))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(k8_relat_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_537,plain,
    ( r2_hidden(X0_41,X0_40) = iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X0_40,X1_40)) != iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(k8_relat_1(X0_40,X1_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_582,plain,
    ( r2_hidden(X0_41,X0_40) = iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X0_40,X1_40)) != iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_537,c_541])).

cnf(c_948,plain,
    ( r1_tarski(k8_relat_1(X0_40,X1_40),X2_40) = iProver_top
    | r2_hidden(sK3(k8_relat_1(X0_40,X1_40),X2_40),X0_40) = iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(k8_relat_1(X0_40,X1_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_582])).

cnf(c_1964,plain,
    ( r1_tarski(k8_relat_1(X0_40,X1_40),X2_40) = iProver_top
    | r2_hidden(sK3(k8_relat_1(X0_40,X1_40),X2_40),X0_40) = iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_948,c_541])).

cnf(c_1061,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(X0_40,X2_40) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0_40,X2_40),sK3(X0_40,X2_40)),X1_40) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_540])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k8_relat_1(X1,X3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_254,plain,
    ( ~ r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(k4_tarski(X0_42,X0_41),X1_40)
    | r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X0_40,X1_40))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(k8_relat_1(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_535,plain,
    ( r2_hidden(X0_41,X0_40) != iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),X1_40) != iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X0_40,X1_40)) = iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(k8_relat_1(X0_40,X1_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_599,plain,
    ( r2_hidden(X0_41,X0_40) != iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),X1_40) != iProver_top
    | r2_hidden(k4_tarski(X0_42,X0_41),k8_relat_1(X0_40,X1_40)) = iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_535,c_541])).

cnf(c_1348,plain,
    ( r1_tarski(X0_40,k8_relat_1(X1_40,X2_40)) = iProver_top
    | r2_hidden(sK3(X0_40,k8_relat_1(X1_40,X2_40)),X1_40) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0_40,k8_relat_1(X1_40,X2_40)),sK3(X0_40,k8_relat_1(X1_40,X2_40))),X2_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X2_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_538])).

cnf(c_2062,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(X0_40,k8_relat_1(X2_40,X1_40)) = iProver_top
    | r2_hidden(sK3(X0_40,k8_relat_1(X2_40,X1_40)),X2_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_1348])).

cnf(c_2790,plain,
    ( r1_tarski(k8_relat_1(X0_40,X1_40),X2_40) != iProver_top
    | r1_tarski(k8_relat_1(X0_40,X1_40),k8_relat_1(X0_40,X2_40)) = iProver_top
    | v1_relat_1(X2_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(k8_relat_1(X0_40,X1_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1964,c_2062])).

cnf(c_2904,plain,
    ( r1_tarski(k8_relat_1(X0_40,X1_40),X2_40) != iProver_top
    | r1_tarski(k8_relat_1(X0_40,X1_40),k8_relat_1(X0_40,X2_40)) = iProver_top
    | v1_relat_1(X2_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2790,c_541])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK4,sK5),k8_relat_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_247,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK4,sK5),k8_relat_1(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_542,plain,
    ( r1_tarski(k8_relat_1(sK4,sK5),k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_2906,plain,
    ( r1_tarski(k8_relat_1(sK4,sK5),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2904,c_542])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2953,plain,
    ( r1_tarski(k8_relat_1(sK4,sK5),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2906,c_14,c_15])).

cnf(c_2958,plain,
    ( r1_tarski(sK5,sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_2953])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,plain,
    ( r1_tarski(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2958,c_16,c_14])).


%------------------------------------------------------------------------------
