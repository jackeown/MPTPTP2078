%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0490+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:25 EST 2020

% Result     : Theorem 1.05s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 ( 269 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f6,plain,(
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

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f22,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(nnf_transformation,[],[f7])).

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

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k7_relat_1(X1,X0),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(X1,X0),X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k7_relat_1(sK5,sK4),sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(k7_relat_1(sK5,sK4),sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f9,f19])).

fof(f32,plain,(
    ~ r1_tarski(k7_relat_1(sK5,sK4),sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k7_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_204,plain,
    ( r2_hidden(k4_tarski(X0_40,X0_41),X0_39)
    | ~ r2_hidden(k4_tarski(X0_40,X0_41),k7_relat_1(X0_39,X1_39))
    | ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(k7_relat_1(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_199,plain,
    ( ~ v1_relat_1(X0_39)
    | v1_relat_1(k7_relat_1(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_275,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ r2_hidden(k4_tarski(X0_40,X0_41),k7_relat_1(X0_39,X1_39))
    | r2_hidden(k4_tarski(X0_40,X0_41),X0_39) ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_199])).

cnf(c_276,plain,
    ( r2_hidden(k4_tarski(X0_40,X0_41),X0_39)
    | ~ r2_hidden(k4_tarski(X0_40,X0_41),k7_relat_1(X0_39,X1_39))
    | ~ v1_relat_1(X0_39) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_716,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK5,sK4),sK5),sK3(k7_relat_1(sK5,sK4),sK5)),k7_relat_1(sK5,sK4))
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK5,sK4),sK5),sK3(k7_relat_1(sK5,sK4),sK5)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_644,plain,
    ( v1_relat_1(k7_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(sK5,sK4),sK5) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_175,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(sK5,sK4) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_176,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK5,sK4),sK5),sK3(k7_relat_1(sK5,sK4),sK5)),sK5)
    | ~ v1_relat_1(k7_relat_1(sK5,sK4)) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_165,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | k7_relat_1(sK5,sK4) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_166,plain,
    ( r2_hidden(k4_tarski(sK2(k7_relat_1(sK5,sK4),sK5),sK3(k7_relat_1(sK5,sK4),sK5)),k7_relat_1(sK5,sK4))
    | ~ v1_relat_1(k7_relat_1(sK5,sK4)) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_716,c_644,c_176,c_166,c_11])).


%------------------------------------------------------------------------------
