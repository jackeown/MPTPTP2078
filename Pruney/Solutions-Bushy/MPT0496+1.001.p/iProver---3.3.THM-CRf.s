%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0496+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:26 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 103 expanded)
%              Number of clauses        :   46 (  46 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :  326 ( 558 expanded)
%              Number of equality atoms :   69 (  95 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f19])).

fof(f33,plain,(
    k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_152,plain,
    ( ~ r2_hidden(sK0(X0_38,X1_38,X2_38),X1_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,X2_38),sK1(X0_38,X1_38,X2_38)),X0_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,X2_38),sK1(X0_38,X1_38,X2_38)),X2_38)
    | ~ v1_relat_1(X2_38)
    | ~ v1_relat_1(X0_38)
    | k7_relat_1(X0_38,X1_38) = X2_38 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1992,plain,
    ( ~ r2_hidden(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),X1_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),X0_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),k5_relat_1(k6_relat_1(X2_38),X3_38))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2_38),X3_38))
    | k7_relat_1(X0_38,X1_38) = k5_relat_1(k6_relat_1(X2_38),X3_38) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_7264,plain,
    ( ~ r2_hidden(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK2)
    | ~ r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),sK3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_7265,plain,
    ( k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3)
    | r2_hidden(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK2) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3)) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),sK3) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7264])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_144,plain,
    ( ~ r2_hidden(X0_39,X0_38)
    | ~ r2_hidden(k4_tarski(X0_39,X0_40),X1_38)
    | r2_hidden(k4_tarski(X0_39,X0_40),k5_relat_1(k6_relat_1(X0_38),X1_38))
    | ~ v1_relat_1(X1_38) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1978,plain,
    ( ~ r2_hidden(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),X1_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),X0_40),X4_38)
    | r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),X0_40),k5_relat_1(k6_relat_1(X1_38),X4_38))
    | ~ v1_relat_1(X4_38) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_2612,plain,
    ( ~ r2_hidden(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),X1_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),X0_38)
    | r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),k5_relat_1(k6_relat_1(X1_38),X0_38))
    | ~ v1_relat_1(X0_38) ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_6617,plain,
    ( ~ r2_hidden(sK0(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38)),sK2)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38)),sK1(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38))),X0_38)
    | r2_hidden(k4_tarski(sK0(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38)),sK1(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38))),k5_relat_1(k6_relat_1(sK2),X0_38))
    | ~ v1_relat_1(X0_38) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_6619,plain,
    ( r2_hidden(sK0(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38)),sK2) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38)),sK1(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38))),X0_38) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38)),sK1(X0_38,sK2,k5_relat_1(k6_relat_1(sK2),X0_38))),k5_relat_1(k6_relat_1(sK2),X0_38)) = iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6617])).

cnf(c_6621,plain,
    ( r2_hidden(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK2) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6619])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X3),X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_143,plain,
    ( r2_hidden(k4_tarski(X0_39,X0_40),X0_38)
    | ~ r2_hidden(k4_tarski(X0_39,X0_40),k5_relat_1(k6_relat_1(X1_38),X0_38))
    | ~ v1_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_560,plain,
    ( r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),X3_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),k5_relat_1(k6_relat_1(X2_38),X3_38))
    | ~ v1_relat_1(X3_38) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_2242,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3))
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_2246,plain,
    ( r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3)) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2242])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_142,plain,
    ( r2_hidden(X0_39,X0_38)
    | ~ r2_hidden(k4_tarski(X0_39,X0_40),k5_relat_1(k6_relat_1(X0_38),X1_38))
    | ~ v1_relat_1(X1_38) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_532,plain,
    ( r2_hidden(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),X2_38)
    | ~ r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),k5_relat_1(k6_relat_1(X2_38),X3_38))
    | ~ v1_relat_1(X3_38) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_2243,plain,
    ( r2_hidden(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK2)
    | ~ r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_2244,plain,
    ( r2_hidden(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK2) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2243])).

cnf(c_7,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_145,plain,
    ( v1_relat_1(k6_relat_1(X0_38)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1406,plain,
    ( v1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_1407,plain,
    ( v1_relat_1(k6_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_146,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | v1_relat_1(k5_relat_1(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_605,plain,
    ( ~ v1_relat_1(X0_38)
    | v1_relat_1(k5_relat_1(k6_relat_1(X1_38),X0_38))
    | ~ v1_relat_1(k6_relat_1(X1_38)) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_809,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_810,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3)) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_151,plain,
    ( r2_hidden(k4_tarski(sK0(X0_38,X1_38,X2_38),sK1(X0_38,X1_38,X2_38)),X2_38)
    | r2_hidden(k4_tarski(sK0(X0_38,X1_38,X2_38),sK1(X0_38,X1_38,X2_38)),X0_38)
    | ~ v1_relat_1(X2_38)
    | ~ v1_relat_1(X0_38)
    | k7_relat_1(X0_38,X1_38) = X2_38 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_559,plain,
    ( r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),X0_38)
    | r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),k5_relat_1(k6_relat_1(X2_38),X3_38))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2_38),X3_38))
    | k7_relat_1(X0_38,X1_38) = k5_relat_1(k6_relat_1(X2_38),X3_38) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_745,plain,
    ( r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3))
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),sK3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_746,plain,
    ( k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3)
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3)) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),sK3) = iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_150,plain,
    ( r2_hidden(sK0(X0_38,X1_38,X2_38),X1_38)
    | r2_hidden(k4_tarski(sK0(X0_38,X1_38,X2_38),sK1(X0_38,X1_38,X2_38)),X2_38)
    | ~ v1_relat_1(X2_38)
    | ~ v1_relat_1(X0_38)
    | k7_relat_1(X0_38,X1_38) = X2_38 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_531,plain,
    ( r2_hidden(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),X1_38)
    | r2_hidden(k4_tarski(sK0(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38)),sK1(X0_38,X1_38,k5_relat_1(k6_relat_1(X2_38),X3_38))),k5_relat_1(k6_relat_1(X2_38),X3_38))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2_38),X3_38))
    | k7_relat_1(X0_38,X1_38) = k5_relat_1(k6_relat_1(X2_38),X3_38) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_725,plain,
    ( r2_hidden(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK2)
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_726,plain,
    ( k7_relat_1(sK3,sK2) = k5_relat_1(k6_relat_1(sK2),sK3)
    | r2_hidden(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK2) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3)),sK1(sK3,sK2,k5_relat_1(k6_relat_1(sK2),sK3))),k5_relat_1(k6_relat_1(sK2),sK3)) = iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK2),sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_11,negated_conjecture,
    ( k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_141,negated_conjecture,
    ( k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7265,c_6621,c_2246,c_2244,c_1407,c_810,c_746,c_726,c_141,c_13])).


%------------------------------------------------------------------------------
