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
% DateTime   : Thu Dec  3 11:53:31 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 185 expanded)
%              Number of clauses        :   62 (  64 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  351 ( 820 expanded)
%              Number of equality atoms :   93 ( 143 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK4(X0),sK3(X0))
        & sK3(X0) != sK4(X0)
        & ~ r2_hidden(sK3(X0),sK4(X0))
        & r2_hidden(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK4(X0),sK3(X0))
          & sK3(X0) != sK4(X0)
          & ~ r2_hidden(sK3(X0),sK4(X0))
          & r2_hidden(sK4(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f41])).

fof(f59,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(X4,X3)
      | X3 = X4
      | r2_hidden(X3,X4)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X3,X0)
      | ~ v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK2(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f58,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK3(X0),sK4(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK3(X0) != sK4(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK4(X0),sK3(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f67,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK5))
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ v3_ordinal1(k3_tarski(sK5))
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f45])).

fof(f72,plain,(
    ~ v3_ordinal1(k3_tarski(sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X2,X0)
    | ~ v2_ordinal1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2143,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK5)),X0)
    | r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5)))
    | ~ r2_hidden(sK4(k3_tarski(sK5)),X0)
    | r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5)))
    | ~ v2_ordinal1(X0)
    | sK3(k3_tarski(sK5)) = sK4(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2146,plain,
    ( sK3(k3_tarski(sK5)) = sK4(k3_tarski(sK5))
    | r2_hidden(sK3(k3_tarski(sK5)),X0) != iProver_top
    | r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5))) = iProver_top
    | r2_hidden(sK4(k3_tarski(sK5)),X0) != iProver_top
    | r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5))) = iProver_top
    | v2_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_2148,plain,
    ( sK3(k3_tarski(sK5)) = sK4(k3_tarski(sK5))
    | r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5))) = iProver_top
    | r2_hidden(sK3(k3_tarski(sK5)),sK5) != iProver_top
    | r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5))) = iProver_top
    | r2_hidden(sK4(k3_tarski(sK5)),sK5) != iProver_top
    | v2_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2146])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1661,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( ~ r1_tarski(sK2(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1656,plain,
    ( r1_tarski(sK2(X0),X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2133,plain,
    ( r2_hidden(sK2(k3_tarski(X0)),X0) != iProver_top
    | v1_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1656])).

cnf(c_2135,plain,
    ( r2_hidden(sK2(k3_tarski(sK5)),sK5) != iProver_top
    | v1_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2118,plain,
    ( r2_hidden(sK4(k3_tarski(sK5)),X0)
    | ~ r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5))
    | ~ r1_tarski(k3_tarski(sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2122,plain,
    ( r2_hidden(sK4(k3_tarski(sK5)),X0) = iProver_top
    | r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
    | r1_tarski(k3_tarski(sK5),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_2124,plain,
    ( r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
    | r2_hidden(sK4(k3_tarski(sK5)),sK5) = iProver_top
    | r1_tarski(k3_tarski(sK5),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_1976,plain,
    ( r2_hidden(sK3(k3_tarski(sK5)),X0)
    | ~ r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5))
    | ~ r1_tarski(k3_tarski(sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1980,plain,
    ( r2_hidden(sK3(k3_tarski(sK5)),X0) = iProver_top
    | r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
    | r1_tarski(k3_tarski(sK5),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_1982,plain,
    ( r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
    | r2_hidden(sK3(k3_tarski(sK5)),sK5) = iProver_top
    | r1_tarski(k3_tarski(sK5),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_16,plain,
    ( r2_hidden(sK3(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1928,plain,
    ( r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5))
    | v2_ordinal1(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1942,plain,
    ( r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5)) = iProver_top
    | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1928])).

cnf(c_15,plain,
    ( r2_hidden(sK4(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1929,plain,
    ( r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5))
    | v2_ordinal1(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1940,plain,
    ( r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5)) = iProver_top
    | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_14,plain,
    ( ~ r2_hidden(sK3(X0),sK4(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1930,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5)))
    | v2_ordinal1(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1938,plain,
    ( r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5))) != iProver_top
    | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_13,plain,
    ( v2_ordinal1(X0)
    | sK3(X0) != sK4(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1931,plain,
    ( v2_ordinal1(k3_tarski(sK5))
    | sK3(k3_tarski(sK5)) != sK4(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1936,plain,
    ( sK3(k3_tarski(sK5)) != sK4(k3_tarski(sK5))
    | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1931])).

cnf(c_12,plain,
    ( ~ r2_hidden(sK4(X0),sK3(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1932,plain,
    ( ~ r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5)))
    | v2_ordinal1(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1934,plain,
    ( r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5))) != iProver_top
    | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_1916,plain,
    ( r2_hidden(sK2(k3_tarski(sK5)),X0)
    | ~ r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5))
    | ~ r1_tarski(k3_tarski(sK5),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1920,plain,
    ( r2_hidden(sK2(k3_tarski(sK5)),X0) = iProver_top
    | r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
    | r1_tarski(k3_tarski(sK5),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_1922,plain,
    ( r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
    | r2_hidden(sK2(k3_tarski(sK5)),sK5) = iProver_top
    | r1_tarski(k3_tarski(sK5),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1892,plain,
    ( r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5))
    | v1_ordinal1(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1897,plain,
    ( r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5)) = iProver_top
    | v1_ordinal1(k3_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1867,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(sK1(X0,X1),X1)
    | ~ v1_ordinal1(X1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1868,plain,
    ( r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(sK1(X0,X1),X1) = iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1867])).

cnf(c_1870,plain,
    ( r2_hidden(sK1(sK5,sK5),sK5) != iProver_top
    | r1_tarski(sK1(sK5,sK5),sK5) = iProver_top
    | v1_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1868])).

cnf(c_18,plain,
    ( ~ v1_ordinal1(X0)
    | v3_ordinal1(X0)
    | ~ v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1828,plain,
    ( ~ v1_ordinal1(k3_tarski(sK5))
    | v3_ordinal1(k3_tarski(sK5))
    | ~ v2_ordinal1(k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1829,plain,
    ( v1_ordinal1(k3_tarski(sK5)) != iProver_top
    | v3_ordinal1(k3_tarski(sK5)) = iProver_top
    | v2_ordinal1(k3_tarski(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1828])).

cnf(c_5,plain,
    ( ~ r1_tarski(sK1(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_72,plain,
    ( r1_tarski(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_74,plain,
    ( r1_tarski(sK1(sK5,sK5),sK5) != iProver_top
    | r1_tarski(k3_tarski(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_69,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_71,plain,
    ( r2_hidden(sK1(sK5,sK5),sK5) = iProver_top
    | r1_tarski(k3_tarski(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_19,plain,
    ( ~ v3_ordinal1(X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_40,plain,
    ( v3_ordinal1(sK5) != iProver_top
    | v2_ordinal1(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_20,plain,
    ( v1_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,plain,
    ( v1_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_37,plain,
    ( v1_ordinal1(sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_24,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,plain,
    ( v3_ordinal1(k3_tarski(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2148,c_2135,c_2124,c_1982,c_1942,c_1940,c_1938,c_1936,c_1934,c_1922,c_1897,c_1870,c_1829,c_74,c_71,c_40,c_37,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:30:34 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.68/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/0.98  
% 1.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.68/0.98  
% 1.68/0.98  ------  iProver source info
% 1.68/0.98  
% 1.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.68/0.98  git: non_committed_changes: false
% 1.68/0.98  git: last_make_outside_of_git: false
% 1.68/0.98  
% 1.68/0.98  ------ 
% 1.68/0.98  
% 1.68/0.98  ------ Input Options
% 1.68/0.98  
% 1.68/0.98  --out_options                           all
% 1.68/0.98  --tptp_safe_out                         true
% 1.68/0.98  --problem_path                          ""
% 1.68/0.98  --include_path                          ""
% 1.68/0.98  --clausifier                            res/vclausify_rel
% 1.68/0.98  --clausifier_options                    --mode clausify
% 1.68/0.98  --stdin                                 false
% 1.68/0.98  --stats_out                             all
% 1.68/0.98  
% 1.68/0.98  ------ General Options
% 1.68/0.98  
% 1.68/0.98  --fof                                   false
% 1.68/0.98  --time_out_real                         305.
% 1.68/0.98  --time_out_virtual                      -1.
% 1.68/0.98  --symbol_type_check                     false
% 1.68/0.98  --clausify_out                          false
% 1.68/0.98  --sig_cnt_out                           false
% 1.68/0.98  --trig_cnt_out                          false
% 1.68/0.98  --trig_cnt_out_tolerance                1.
% 1.68/0.98  --trig_cnt_out_sk_spl                   false
% 1.68/0.98  --abstr_cl_out                          false
% 1.68/0.98  
% 1.68/0.98  ------ Global Options
% 1.68/0.98  
% 1.68/0.98  --schedule                              default
% 1.68/0.98  --add_important_lit                     false
% 1.68/0.98  --prop_solver_per_cl                    1000
% 1.68/0.98  --min_unsat_core                        false
% 1.68/0.98  --soft_assumptions                      false
% 1.68/0.98  --soft_lemma_size                       3
% 1.68/0.98  --prop_impl_unit_size                   0
% 1.68/0.98  --prop_impl_unit                        []
% 1.68/0.98  --share_sel_clauses                     true
% 1.68/0.98  --reset_solvers                         false
% 1.68/0.98  --bc_imp_inh                            [conj_cone]
% 1.68/0.98  --conj_cone_tolerance                   3.
% 1.68/0.98  --extra_neg_conj                        none
% 1.68/0.98  --large_theory_mode                     true
% 1.68/0.98  --prolific_symb_bound                   200
% 1.68/0.98  --lt_threshold                          2000
% 1.68/0.98  --clause_weak_htbl                      true
% 1.68/0.98  --gc_record_bc_elim                     false
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing Options
% 1.68/0.98  
% 1.68/0.98  --preprocessing_flag                    true
% 1.68/0.98  --time_out_prep_mult                    0.1
% 1.68/0.98  --splitting_mode                        input
% 1.68/0.98  --splitting_grd                         true
% 1.68/0.98  --splitting_cvd                         false
% 1.68/0.98  --splitting_cvd_svl                     false
% 1.68/0.98  --splitting_nvd                         32
% 1.68/0.98  --sub_typing                            true
% 1.68/0.98  --prep_gs_sim                           true
% 1.68/0.98  --prep_unflatten                        true
% 1.68/0.98  --prep_res_sim                          true
% 1.68/0.98  --prep_upred                            true
% 1.68/0.98  --prep_sem_filter                       exhaustive
% 1.68/0.98  --prep_sem_filter_out                   false
% 1.68/0.98  --pred_elim                             true
% 1.68/0.98  --res_sim_input                         true
% 1.68/0.98  --eq_ax_congr_red                       true
% 1.68/0.98  --pure_diseq_elim                       true
% 1.68/0.98  --brand_transform                       false
% 1.68/0.98  --non_eq_to_eq                          false
% 1.68/0.98  --prep_def_merge                        true
% 1.68/0.98  --prep_def_merge_prop_impl              false
% 1.68/0.98  --prep_def_merge_mbd                    true
% 1.68/0.98  --prep_def_merge_tr_red                 false
% 1.68/0.98  --prep_def_merge_tr_cl                  false
% 1.68/0.98  --smt_preprocessing                     true
% 1.68/0.98  --smt_ac_axioms                         fast
% 1.68/0.98  --preprocessed_out                      false
% 1.68/0.98  --preprocessed_stats                    false
% 1.68/0.98  
% 1.68/0.98  ------ Abstraction refinement Options
% 1.68/0.98  
% 1.68/0.98  --abstr_ref                             []
% 1.68/0.98  --abstr_ref_prep                        false
% 1.68/0.98  --abstr_ref_until_sat                   false
% 1.68/0.98  --abstr_ref_sig_restrict                funpre
% 1.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.98  --abstr_ref_under                       []
% 1.68/0.98  
% 1.68/0.98  ------ SAT Options
% 1.68/0.98  
% 1.68/0.98  --sat_mode                              false
% 1.68/0.98  --sat_fm_restart_options                ""
% 1.68/0.98  --sat_gr_def                            false
% 1.68/0.98  --sat_epr_types                         true
% 1.68/0.98  --sat_non_cyclic_types                  false
% 1.68/0.98  --sat_finite_models                     false
% 1.68/0.98  --sat_fm_lemmas                         false
% 1.68/0.98  --sat_fm_prep                           false
% 1.68/0.98  --sat_fm_uc_incr                        true
% 1.68/0.98  --sat_out_model                         small
% 1.68/0.98  --sat_out_clauses                       false
% 1.68/0.98  
% 1.68/0.98  ------ QBF Options
% 1.68/0.98  
% 1.68/0.98  --qbf_mode                              false
% 1.68/0.98  --qbf_elim_univ                         false
% 1.68/0.98  --qbf_dom_inst                          none
% 1.68/0.98  --qbf_dom_pre_inst                      false
% 1.68/0.98  --qbf_sk_in                             false
% 1.68/0.98  --qbf_pred_elim                         true
% 1.68/0.98  --qbf_split                             512
% 1.68/0.98  
% 1.68/0.98  ------ BMC1 Options
% 1.68/0.98  
% 1.68/0.98  --bmc1_incremental                      false
% 1.68/0.98  --bmc1_axioms                           reachable_all
% 1.68/0.98  --bmc1_min_bound                        0
% 1.68/0.98  --bmc1_max_bound                        -1
% 1.68/0.98  --bmc1_max_bound_default                -1
% 1.68/0.98  --bmc1_symbol_reachability              true
% 1.68/0.98  --bmc1_property_lemmas                  false
% 1.68/0.98  --bmc1_k_induction                      false
% 1.68/0.98  --bmc1_non_equiv_states                 false
% 1.68/0.98  --bmc1_deadlock                         false
% 1.68/0.98  --bmc1_ucm                              false
% 1.68/0.98  --bmc1_add_unsat_core                   none
% 1.68/0.98  --bmc1_unsat_core_children              false
% 1.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.98  --bmc1_out_stat                         full
% 1.68/0.98  --bmc1_ground_init                      false
% 1.68/0.98  --bmc1_pre_inst_next_state              false
% 1.68/0.98  --bmc1_pre_inst_state                   false
% 1.68/0.98  --bmc1_pre_inst_reach_state             false
% 1.68/0.98  --bmc1_out_unsat_core                   false
% 1.68/0.98  --bmc1_aig_witness_out                  false
% 1.68/0.98  --bmc1_verbose                          false
% 1.68/0.98  --bmc1_dump_clauses_tptp                false
% 1.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.98  --bmc1_dump_file                        -
% 1.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.98  --bmc1_ucm_extend_mode                  1
% 1.68/0.98  --bmc1_ucm_init_mode                    2
% 1.68/0.98  --bmc1_ucm_cone_mode                    none
% 1.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.98  --bmc1_ucm_relax_model                  4
% 1.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.98  --bmc1_ucm_layered_model                none
% 1.68/0.98  --bmc1_ucm_max_lemma_size               10
% 1.68/0.98  
% 1.68/0.98  ------ AIG Options
% 1.68/0.98  
% 1.68/0.98  --aig_mode                              false
% 1.68/0.98  
% 1.68/0.98  ------ Instantiation Options
% 1.68/0.98  
% 1.68/0.98  --instantiation_flag                    true
% 1.68/0.98  --inst_sos_flag                         false
% 1.68/0.98  --inst_sos_phase                        true
% 1.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel_side                     num_symb
% 1.68/0.98  --inst_solver_per_active                1400
% 1.68/0.98  --inst_solver_calls_frac                1.
% 1.68/0.98  --inst_passive_queue_type               priority_queues
% 1.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.98  --inst_passive_queues_freq              [25;2]
% 1.68/0.98  --inst_dismatching                      true
% 1.68/0.98  --inst_eager_unprocessed_to_passive     true
% 1.68/0.98  --inst_prop_sim_given                   true
% 1.68/0.98  --inst_prop_sim_new                     false
% 1.68/0.98  --inst_subs_new                         false
% 1.68/0.98  --inst_eq_res_simp                      false
% 1.68/0.98  --inst_subs_given                       false
% 1.68/0.98  --inst_orphan_elimination               true
% 1.68/0.98  --inst_learning_loop_flag               true
% 1.68/0.98  --inst_learning_start                   3000
% 1.68/0.98  --inst_learning_factor                  2
% 1.68/0.98  --inst_start_prop_sim_after_learn       3
% 1.68/0.98  --inst_sel_renew                        solver
% 1.68/0.98  --inst_lit_activity_flag                true
% 1.68/0.98  --inst_restr_to_given                   false
% 1.68/0.98  --inst_activity_threshold               500
% 1.68/0.98  --inst_out_proof                        true
% 1.68/0.98  
% 1.68/0.98  ------ Resolution Options
% 1.68/0.98  
% 1.68/0.98  --resolution_flag                       true
% 1.68/0.98  --res_lit_sel                           adaptive
% 1.68/0.98  --res_lit_sel_side                      none
% 1.68/0.98  --res_ordering                          kbo
% 1.68/0.98  --res_to_prop_solver                    active
% 1.68/0.98  --res_prop_simpl_new                    false
% 1.68/0.98  --res_prop_simpl_given                  true
% 1.68/0.98  --res_passive_queue_type                priority_queues
% 1.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.98  --res_passive_queues_freq               [15;5]
% 1.68/0.98  --res_forward_subs                      full
% 1.68/0.98  --res_backward_subs                     full
% 1.68/0.98  --res_forward_subs_resolution           true
% 1.68/0.98  --res_backward_subs_resolution          true
% 1.68/0.98  --res_orphan_elimination                true
% 1.68/0.98  --res_time_limit                        2.
% 1.68/0.98  --res_out_proof                         true
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Options
% 1.68/0.98  
% 1.68/0.98  --superposition_flag                    true
% 1.68/0.98  --sup_passive_queue_type                priority_queues
% 1.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.98  --demod_completeness_check              fast
% 1.68/0.98  --demod_use_ground                      true
% 1.68/0.98  --sup_to_prop_solver                    passive
% 1.68/0.98  --sup_prop_simpl_new                    true
% 1.68/0.98  --sup_prop_simpl_given                  true
% 1.68/0.98  --sup_fun_splitting                     false
% 1.68/0.98  --sup_smt_interval                      50000
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Simplification Setup
% 1.68/0.98  
% 1.68/0.98  --sup_indices_passive                   []
% 1.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_full_bw                           [BwDemod]
% 1.68/0.98  --sup_immed_triv                        [TrivRules]
% 1.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_immed_bw_main                     []
% 1.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.98  
% 1.68/0.98  ------ Combination Options
% 1.68/0.98  
% 1.68/0.98  --comb_res_mult                         3
% 1.68/0.98  --comb_sup_mult                         2
% 1.68/0.98  --comb_inst_mult                        10
% 1.68/0.98  
% 1.68/0.98  ------ Debug Options
% 1.68/0.98  
% 1.68/0.98  --dbg_backtrace                         false
% 1.68/0.98  --dbg_dump_prop_clauses                 false
% 1.68/0.98  --dbg_dump_prop_clauses_file            -
% 1.68/0.98  --dbg_out_stat                          false
% 1.68/0.98  ------ Parsing...
% 1.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.68/0.98  ------ Proving...
% 1.68/0.98  ------ Problem Properties 
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  clauses                                 23
% 1.68/0.98  conjectures                             2
% 1.68/0.98  EPR                                     10
% 1.68/0.98  Horn                                    16
% 1.68/0.98  unary                                   2
% 1.68/0.98  binary                                  14
% 1.68/0.98  lits                                    57
% 1.68/0.98  lits eq                                 3
% 1.68/0.98  fd_pure                                 0
% 1.68/0.98  fd_pseudo                               0
% 1.68/0.98  fd_cond                                 0
% 1.68/0.98  fd_pseudo_cond                          2
% 1.68/0.98  AC symbols                              0
% 1.68/0.98  
% 1.68/0.98  ------ Schedule dynamic 5 is on 
% 1.68/0.98  
% 1.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  ------ 
% 1.68/0.98  Current options:
% 1.68/0.98  ------ 
% 1.68/0.98  
% 1.68/0.98  ------ Input Options
% 1.68/0.98  
% 1.68/0.98  --out_options                           all
% 1.68/0.98  --tptp_safe_out                         true
% 1.68/0.98  --problem_path                          ""
% 1.68/0.98  --include_path                          ""
% 1.68/0.98  --clausifier                            res/vclausify_rel
% 1.68/0.98  --clausifier_options                    --mode clausify
% 1.68/0.98  --stdin                                 false
% 1.68/0.98  --stats_out                             all
% 1.68/0.98  
% 1.68/0.98  ------ General Options
% 1.68/0.98  
% 1.68/0.98  --fof                                   false
% 1.68/0.98  --time_out_real                         305.
% 1.68/0.98  --time_out_virtual                      -1.
% 1.68/0.98  --symbol_type_check                     false
% 1.68/0.98  --clausify_out                          false
% 1.68/0.98  --sig_cnt_out                           false
% 1.68/0.98  --trig_cnt_out                          false
% 1.68/0.98  --trig_cnt_out_tolerance                1.
% 1.68/0.98  --trig_cnt_out_sk_spl                   false
% 1.68/0.98  --abstr_cl_out                          false
% 1.68/0.98  
% 1.68/0.98  ------ Global Options
% 1.68/0.98  
% 1.68/0.98  --schedule                              default
% 1.68/0.98  --add_important_lit                     false
% 1.68/0.98  --prop_solver_per_cl                    1000
% 1.68/0.98  --min_unsat_core                        false
% 1.68/0.98  --soft_assumptions                      false
% 1.68/0.98  --soft_lemma_size                       3
% 1.68/0.98  --prop_impl_unit_size                   0
% 1.68/0.98  --prop_impl_unit                        []
% 1.68/0.98  --share_sel_clauses                     true
% 1.68/0.98  --reset_solvers                         false
% 1.68/0.98  --bc_imp_inh                            [conj_cone]
% 1.68/0.98  --conj_cone_tolerance                   3.
% 1.68/0.98  --extra_neg_conj                        none
% 1.68/0.98  --large_theory_mode                     true
% 1.68/0.98  --prolific_symb_bound                   200
% 1.68/0.98  --lt_threshold                          2000
% 1.68/0.98  --clause_weak_htbl                      true
% 1.68/0.98  --gc_record_bc_elim                     false
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing Options
% 1.68/0.98  
% 1.68/0.98  --preprocessing_flag                    true
% 1.68/0.98  --time_out_prep_mult                    0.1
% 1.68/0.98  --splitting_mode                        input
% 1.68/0.98  --splitting_grd                         true
% 1.68/0.98  --splitting_cvd                         false
% 1.68/0.98  --splitting_cvd_svl                     false
% 1.68/0.98  --splitting_nvd                         32
% 1.68/0.98  --sub_typing                            true
% 1.68/0.98  --prep_gs_sim                           true
% 1.68/0.98  --prep_unflatten                        true
% 1.68/0.98  --prep_res_sim                          true
% 1.68/0.98  --prep_upred                            true
% 1.68/0.98  --prep_sem_filter                       exhaustive
% 1.68/0.98  --prep_sem_filter_out                   false
% 1.68/0.98  --pred_elim                             true
% 1.68/0.98  --res_sim_input                         true
% 1.68/0.98  --eq_ax_congr_red                       true
% 1.68/0.98  --pure_diseq_elim                       true
% 1.68/0.98  --brand_transform                       false
% 1.68/0.98  --non_eq_to_eq                          false
% 1.68/0.98  --prep_def_merge                        true
% 1.68/0.98  --prep_def_merge_prop_impl              false
% 1.68/0.98  --prep_def_merge_mbd                    true
% 1.68/0.98  --prep_def_merge_tr_red                 false
% 1.68/0.98  --prep_def_merge_tr_cl                  false
% 1.68/0.98  --smt_preprocessing                     true
% 1.68/0.98  --smt_ac_axioms                         fast
% 1.68/0.98  --preprocessed_out                      false
% 1.68/0.98  --preprocessed_stats                    false
% 1.68/0.98  
% 1.68/0.98  ------ Abstraction refinement Options
% 1.68/0.98  
% 1.68/0.98  --abstr_ref                             []
% 1.68/0.98  --abstr_ref_prep                        false
% 1.68/0.98  --abstr_ref_until_sat                   false
% 1.68/0.98  --abstr_ref_sig_restrict                funpre
% 1.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.98  --abstr_ref_under                       []
% 1.68/0.98  
% 1.68/0.98  ------ SAT Options
% 1.68/0.98  
% 1.68/0.98  --sat_mode                              false
% 1.68/0.98  --sat_fm_restart_options                ""
% 1.68/0.98  --sat_gr_def                            false
% 1.68/0.98  --sat_epr_types                         true
% 1.68/0.98  --sat_non_cyclic_types                  false
% 1.68/0.98  --sat_finite_models                     false
% 1.68/0.98  --sat_fm_lemmas                         false
% 1.68/0.98  --sat_fm_prep                           false
% 1.68/0.98  --sat_fm_uc_incr                        true
% 1.68/0.98  --sat_out_model                         small
% 1.68/0.98  --sat_out_clauses                       false
% 1.68/0.98  
% 1.68/0.98  ------ QBF Options
% 1.68/0.98  
% 1.68/0.98  --qbf_mode                              false
% 1.68/0.98  --qbf_elim_univ                         false
% 1.68/0.98  --qbf_dom_inst                          none
% 1.68/0.98  --qbf_dom_pre_inst                      false
% 1.68/0.98  --qbf_sk_in                             false
% 1.68/0.98  --qbf_pred_elim                         true
% 1.68/0.98  --qbf_split                             512
% 1.68/0.98  
% 1.68/0.98  ------ BMC1 Options
% 1.68/0.98  
% 1.68/0.98  --bmc1_incremental                      false
% 1.68/0.98  --bmc1_axioms                           reachable_all
% 1.68/0.98  --bmc1_min_bound                        0
% 1.68/0.98  --bmc1_max_bound                        -1
% 1.68/0.98  --bmc1_max_bound_default                -1
% 1.68/0.98  --bmc1_symbol_reachability              true
% 1.68/0.98  --bmc1_property_lemmas                  false
% 1.68/0.98  --bmc1_k_induction                      false
% 1.68/0.98  --bmc1_non_equiv_states                 false
% 1.68/0.98  --bmc1_deadlock                         false
% 1.68/0.98  --bmc1_ucm                              false
% 1.68/0.98  --bmc1_add_unsat_core                   none
% 1.68/0.98  --bmc1_unsat_core_children              false
% 1.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.98  --bmc1_out_stat                         full
% 1.68/0.98  --bmc1_ground_init                      false
% 1.68/0.98  --bmc1_pre_inst_next_state              false
% 1.68/0.98  --bmc1_pre_inst_state                   false
% 1.68/0.98  --bmc1_pre_inst_reach_state             false
% 1.68/0.98  --bmc1_out_unsat_core                   false
% 1.68/0.98  --bmc1_aig_witness_out                  false
% 1.68/0.98  --bmc1_verbose                          false
% 1.68/0.98  --bmc1_dump_clauses_tptp                false
% 1.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.98  --bmc1_dump_file                        -
% 1.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.98  --bmc1_ucm_extend_mode                  1
% 1.68/0.98  --bmc1_ucm_init_mode                    2
% 1.68/0.98  --bmc1_ucm_cone_mode                    none
% 1.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.98  --bmc1_ucm_relax_model                  4
% 1.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.98  --bmc1_ucm_layered_model                none
% 1.68/0.98  --bmc1_ucm_max_lemma_size               10
% 1.68/0.98  
% 1.68/0.98  ------ AIG Options
% 1.68/0.98  
% 1.68/0.98  --aig_mode                              false
% 1.68/0.98  
% 1.68/0.98  ------ Instantiation Options
% 1.68/0.98  
% 1.68/0.98  --instantiation_flag                    true
% 1.68/0.98  --inst_sos_flag                         false
% 1.68/0.98  --inst_sos_phase                        true
% 1.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel_side                     none
% 1.68/0.98  --inst_solver_per_active                1400
% 1.68/0.98  --inst_solver_calls_frac                1.
% 1.68/0.98  --inst_passive_queue_type               priority_queues
% 1.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.98  --inst_passive_queues_freq              [25;2]
% 1.68/0.98  --inst_dismatching                      true
% 1.68/0.98  --inst_eager_unprocessed_to_passive     true
% 1.68/0.98  --inst_prop_sim_given                   true
% 1.68/0.98  --inst_prop_sim_new                     false
% 1.68/0.98  --inst_subs_new                         false
% 1.68/0.98  --inst_eq_res_simp                      false
% 1.68/0.98  --inst_subs_given                       false
% 1.68/0.98  --inst_orphan_elimination               true
% 1.68/0.98  --inst_learning_loop_flag               true
% 1.68/0.98  --inst_learning_start                   3000
% 1.68/0.98  --inst_learning_factor                  2
% 1.68/0.98  --inst_start_prop_sim_after_learn       3
% 1.68/0.98  --inst_sel_renew                        solver
% 1.68/0.98  --inst_lit_activity_flag                true
% 1.68/0.98  --inst_restr_to_given                   false
% 1.68/0.98  --inst_activity_threshold               500
% 1.68/0.98  --inst_out_proof                        true
% 1.68/0.98  
% 1.68/0.98  ------ Resolution Options
% 1.68/0.98  
% 1.68/0.98  --resolution_flag                       false
% 1.68/0.98  --res_lit_sel                           adaptive
% 1.68/0.98  --res_lit_sel_side                      none
% 1.68/0.98  --res_ordering                          kbo
% 1.68/0.98  --res_to_prop_solver                    active
% 1.68/0.98  --res_prop_simpl_new                    false
% 1.68/0.98  --res_prop_simpl_given                  true
% 1.68/0.98  --res_passive_queue_type                priority_queues
% 1.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.98  --res_passive_queues_freq               [15;5]
% 1.68/0.98  --res_forward_subs                      full
% 1.68/0.98  --res_backward_subs                     full
% 1.68/0.98  --res_forward_subs_resolution           true
% 1.68/0.98  --res_backward_subs_resolution          true
% 1.68/0.98  --res_orphan_elimination                true
% 1.68/0.98  --res_time_limit                        2.
% 1.68/0.98  --res_out_proof                         true
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Options
% 1.68/0.98  
% 1.68/0.98  --superposition_flag                    true
% 1.68/0.98  --sup_passive_queue_type                priority_queues
% 1.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.98  --demod_completeness_check              fast
% 1.68/0.98  --demod_use_ground                      true
% 1.68/0.98  --sup_to_prop_solver                    passive
% 1.68/0.98  --sup_prop_simpl_new                    true
% 1.68/0.98  --sup_prop_simpl_given                  true
% 1.68/0.98  --sup_fun_splitting                     false
% 1.68/0.98  --sup_smt_interval                      50000
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Simplification Setup
% 1.68/0.98  
% 1.68/0.98  --sup_indices_passive                   []
% 1.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_full_bw                           [BwDemod]
% 1.68/0.98  --sup_immed_triv                        [TrivRules]
% 1.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_immed_bw_main                     []
% 1.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.98  
% 1.68/0.98  ------ Combination Options
% 1.68/0.98  
% 1.68/0.98  --comb_res_mult                         3
% 1.68/0.98  --comb_sup_mult                         2
% 1.68/0.98  --comb_inst_mult                        10
% 1.68/0.98  
% 1.68/0.98  ------ Debug Options
% 1.68/0.98  
% 1.68/0.98  --dbg_backtrace                         false
% 1.68/0.98  --dbg_dump_prop_clauses                 false
% 1.68/0.98  --dbg_dump_prop_clauses_file            -
% 1.68/0.98  --dbg_out_stat                          false
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  ------ Proving...
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  % SZS status Theorem for theBenchmark.p
% 1.68/0.98  
% 1.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.68/0.98  
% 1.68/0.98  fof(f7,axiom,(
% 1.68/0.98    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 1.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.68/0.98  
% 1.68/0.98  fof(f22,plain,(
% 1.68/0.98    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)))),
% 1.68/0.98    inference(ennf_transformation,[],[f7])).
% 1.68/0.98  
% 1.68/0.98  fof(f39,plain,(
% 1.68/0.98    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)) | ~v2_ordinal1(X0)))),
% 1.68/0.98    inference(nnf_transformation,[],[f22])).
% 1.68/0.98  
% 1.68/0.98  fof(f40,plain,(
% 1.68/0.98    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 1.68/0.98    inference(rectify,[],[f39])).
% 1.68/0.98  
% 1.68/0.98  fof(f41,plain,(
% 1.68/0.98    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(sK4(X0),sK3(X0)) & sK3(X0) != sK4(X0) & ~r2_hidden(sK3(X0),sK4(X0)) & r2_hidden(sK4(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 1.68/0.98    introduced(choice_axiom,[])).
% 1.68/0.98  
% 1.68/0.98  fof(f42,plain,(
% 1.68/0.98    ! [X0] : ((v2_ordinal1(X0) | (~r2_hidden(sK4(X0),sK3(X0)) & sK3(X0) != sK4(X0) & ~r2_hidden(sK3(X0),sK4(X0)) & r2_hidden(sK4(X0),X0) & r2_hidden(sK3(X0),X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 1.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f41])).
% 1.68/0.98  
% 1.68/0.98  fof(f59,plain,(
% 1.68/0.98    ( ! [X4,X0,X3] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0) | ~v2_ordinal1(X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f42])).
% 1.68/0.98  
% 1.68/0.98  fof(f3,axiom,(
% 1.68/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.68/0.98  
% 1.68/0.98  fof(f18,plain,(
% 1.68/0.98    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.68/0.98    inference(ennf_transformation,[],[f3])).
% 1.68/0.98  
% 1.68/0.98  fof(f51,plain,(
% 1.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f18])).
% 1.68/0.98  
% 1.68/0.98  fof(f6,axiom,(
% 1.68/0.98    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.68/0.98  
% 1.68/0.98  fof(f21,plain,(
% 1.68/0.98    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 1.68/0.98    inference(ennf_transformation,[],[f6])).
% 1.68/0.98  
% 1.68/0.98  fof(f35,plain,(
% 1.68/0.98    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 1.68/0.98    inference(nnf_transformation,[],[f21])).
% 1.68/0.98  
% 1.68/0.98  fof(f36,plain,(
% 1.68/0.98    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 1.68/0.98    inference(rectify,[],[f35])).
% 1.68/0.98  
% 1.68/0.98  fof(f37,plain,(
% 1.68/0.98    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 1.68/0.98    introduced(choice_axiom,[])).
% 1.68/0.98  
% 1.68/0.98  fof(f38,plain,(
% 1.68/0.98    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 1.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 1.68/0.98  
% 1.68/0.98  fof(f58,plain,(
% 1.68/0.98    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK2(X0),X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f38])).
% 1.68/0.98  
% 1.68/0.98  fof(f1,axiom,(
% 1.68/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.68/0.98  
% 1.68/0.98  fof(f15,plain,(
% 1.68/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.68/0.98    inference(ennf_transformation,[],[f1])).
% 1.68/0.98  
% 1.68/0.98  fof(f29,plain,(
% 1.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.68/0.98    inference(nnf_transformation,[],[f15])).
% 1.68/0.98  
% 1.68/0.98  fof(f30,plain,(
% 1.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.68/0.98    inference(rectify,[],[f29])).
% 1.68/0.98  
% 1.68/0.98  fof(f31,plain,(
% 1.68/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.68/0.98    introduced(choice_axiom,[])).
% 1.68/0.98  
% 1.68/0.98  fof(f32,plain,(
% 1.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 1.68/0.98  
% 1.68/0.98  fof(f47,plain,(
% 1.68/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f32])).
% 1.68/0.98  
% 1.68/0.98  fof(f60,plain,(
% 1.68/0.98    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f42])).
% 1.68/0.98  
% 1.68/0.98  fof(f61,plain,(
% 1.68/0.98    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f42])).
% 1.68/0.98  
% 1.68/0.98  fof(f62,plain,(
% 1.68/0.98    ( ! [X0] : (v2_ordinal1(X0) | ~r2_hidden(sK3(X0),sK4(X0))) )),
% 1.68/0.98    inference(cnf_transformation,[],[f42])).
% 1.68/0.98  
% 1.68/0.98  fof(f63,plain,(
% 1.68/0.98    ( ! [X0] : (v2_ordinal1(X0) | sK3(X0) != sK4(X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f42])).
% 1.68/0.98  
% 1.68/0.98  fof(f64,plain,(
% 1.68/0.98    ( ! [X0] : (v2_ordinal1(X0) | ~r2_hidden(sK4(X0),sK3(X0))) )),
% 1.68/0.98    inference(cnf_transformation,[],[f42])).
% 1.68/0.98  
% 1.68/0.98  fof(f57,plain,(
% 1.68/0.98    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK2(X0),X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f38])).
% 1.68/0.98  
% 1.68/0.98  fof(f56,plain,(
% 1.68/0.98    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f38])).
% 1.68/0.98  
% 1.68/0.98  fof(f8,axiom,(
% 1.68/0.98    ! [X0] : (v3_ordinal1(X0) <=> (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.68/0.98  
% 1.68/0.98  fof(f43,plain,(
% 1.68/0.98    ! [X0] : ((v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0))) & ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0)))),
% 1.68/0.98    inference(nnf_transformation,[],[f8])).
% 1.68/0.98  
% 1.68/0.98  fof(f44,plain,(
% 1.68/0.98    ! [X0] : ((v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0)) & ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0)))),
% 1.68/0.98    inference(flattening,[],[f43])).
% 1.68/0.98  
% 1.68/0.98  fof(f67,plain,(
% 1.68/0.98    ( ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f44])).
% 1.68/0.98  
% 1.68/0.98  fof(f4,axiom,(
% 1.68/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.68/0.98  
% 1.68/0.98  fof(f19,plain,(
% 1.68/0.98    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.68/0.98    inference(ennf_transformation,[],[f4])).
% 1.68/0.98  
% 1.68/0.98  fof(f33,plain,(
% 1.68/0.98    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.68/0.98    introduced(choice_axiom,[])).
% 1.68/0.98  
% 1.68/0.98  fof(f34,plain,(
% 1.68/0.98    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f33])).
% 1.68/0.98  
% 1.68/0.98  fof(f53,plain,(
% 1.68/0.98    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK1(X0,X1),X1)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f34])).
% 1.68/0.98  
% 1.68/0.98  fof(f52,plain,(
% 1.68/0.98    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f34])).
% 1.68/0.98  
% 1.68/0.98  fof(f66,plain,(
% 1.68/0.98    ( ! [X0] : (v2_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f44])).
% 1.68/0.98  
% 1.68/0.98  fof(f65,plain,(
% 1.68/0.98    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.68/0.98    inference(cnf_transformation,[],[f44])).
% 1.68/0.98  
% 1.68/0.98  fof(f12,conjecture,(
% 1.68/0.98    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.68/0.98  
% 1.68/0.98  fof(f13,negated_conjecture,(
% 1.68/0.98    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.68/0.98    inference(negated_conjecture,[],[f12])).
% 1.68/0.98  
% 1.68/0.98  fof(f28,plain,(
% 1.68/0.98    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 1.68/0.98    inference(ennf_transformation,[],[f13])).
% 1.68/0.98  
% 1.68/0.98  fof(f45,plain,(
% 1.68/0.98    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0)) => (~v3_ordinal1(k3_tarski(sK5)) & v3_ordinal1(sK5))),
% 1.68/0.98    introduced(choice_axiom,[])).
% 1.68/0.98  
% 1.68/0.98  fof(f46,plain,(
% 1.68/0.98    ~v3_ordinal1(k3_tarski(sK5)) & v3_ordinal1(sK5)),
% 1.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f45])).
% 1.68/0.98  
% 1.68/0.98  fof(f72,plain,(
% 1.68/0.98    ~v3_ordinal1(k3_tarski(sK5))),
% 1.68/0.98    inference(cnf_transformation,[],[f46])).
% 1.68/0.98  
% 1.68/0.98  fof(f71,plain,(
% 1.68/0.98    v3_ordinal1(sK5)),
% 1.68/0.98    inference(cnf_transformation,[],[f46])).
% 1.68/0.98  
% 1.68/0.98  cnf(c_17,plain,
% 1.68/0.98      ( ~ r2_hidden(X0,X1)
% 1.68/0.98      | ~ r2_hidden(X2,X1)
% 1.68/0.98      | r2_hidden(X0,X2)
% 1.68/0.98      | r2_hidden(X2,X0)
% 1.68/0.98      | ~ v2_ordinal1(X1)
% 1.68/0.98      | X2 = X0 ),
% 1.68/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2143,plain,
% 1.68/0.98      ( ~ r2_hidden(sK3(k3_tarski(sK5)),X0)
% 1.68/0.98      | r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5)))
% 1.68/0.98      | ~ r2_hidden(sK4(k3_tarski(sK5)),X0)
% 1.68/0.98      | r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5)))
% 1.68/0.98      | ~ v2_ordinal1(X0)
% 1.68/0.98      | sK3(k3_tarski(sK5)) = sK4(k3_tarski(sK5)) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2146,plain,
% 1.68/0.98      ( sK3(k3_tarski(sK5)) = sK4(k3_tarski(sK5))
% 1.68/0.98      | r2_hidden(sK3(k3_tarski(sK5)),X0) != iProver_top
% 1.68/0.98      | r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5))) = iProver_top
% 1.68/0.98      | r2_hidden(sK4(k3_tarski(sK5)),X0) != iProver_top
% 1.68/0.98      | r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5))) = iProver_top
% 1.68/0.98      | v2_ordinal1(X0) != iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_2143]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2148,plain,
% 1.68/0.98      ( sK3(k3_tarski(sK5)) = sK4(k3_tarski(sK5))
% 1.68/0.98      | r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5))) = iProver_top
% 1.68/0.98      | r2_hidden(sK3(k3_tarski(sK5)),sK5) != iProver_top
% 1.68/0.98      | r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5))) = iProver_top
% 1.68/0.98      | r2_hidden(sK4(k3_tarski(sK5)),sK5) != iProver_top
% 1.68/0.98      | v2_ordinal1(sK5) != iProver_top ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_2146]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_4,plain,
% 1.68/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 1.68/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1661,plain,
% 1.68/0.98      ( r2_hidden(X0,X1) != iProver_top
% 1.68/0.98      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_9,plain,
% 1.68/0.98      ( ~ r1_tarski(sK2(X0),X0) | v1_ordinal1(X0) ),
% 1.68/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1656,plain,
% 1.68/0.98      ( r1_tarski(sK2(X0),X0) != iProver_top
% 1.68/0.98      | v1_ordinal1(X0) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2133,plain,
% 1.68/0.98      ( r2_hidden(sK2(k3_tarski(X0)),X0) != iProver_top
% 1.68/0.98      | v1_ordinal1(k3_tarski(X0)) = iProver_top ),
% 1.68/0.98      inference(superposition,[status(thm)],[c_1661,c_1656]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2135,plain,
% 1.68/0.98      ( r2_hidden(sK2(k3_tarski(sK5)),sK5) != iProver_top
% 1.68/0.98      | v1_ordinal1(k3_tarski(sK5)) = iProver_top ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_2133]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2,plain,
% 1.68/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.68/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2118,plain,
% 1.68/0.98      ( r2_hidden(sK4(k3_tarski(sK5)),X0)
% 1.68/0.98      | ~ r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5))
% 1.68/0.98      | ~ r1_tarski(k3_tarski(sK5),X0) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2122,plain,
% 1.68/0.98      ( r2_hidden(sK4(k3_tarski(sK5)),X0) = iProver_top
% 1.68/0.98      | r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
% 1.68/0.98      | r1_tarski(k3_tarski(sK5),X0) != iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_2124,plain,
% 1.68/0.98      ( r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
% 1.68/0.98      | r2_hidden(sK4(k3_tarski(sK5)),sK5) = iProver_top
% 1.68/0.98      | r1_tarski(k3_tarski(sK5),sK5) != iProver_top ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_2122]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1976,plain,
% 1.68/0.98      ( r2_hidden(sK3(k3_tarski(sK5)),X0)
% 1.68/0.98      | ~ r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5))
% 1.68/0.98      | ~ r1_tarski(k3_tarski(sK5),X0) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1980,plain,
% 1.68/0.98      ( r2_hidden(sK3(k3_tarski(sK5)),X0) = iProver_top
% 1.68/0.98      | r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
% 1.68/0.98      | r1_tarski(k3_tarski(sK5),X0) != iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1976]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1982,plain,
% 1.68/0.98      ( r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
% 1.68/0.98      | r2_hidden(sK3(k3_tarski(sK5)),sK5) = iProver_top
% 1.68/0.98      | r1_tarski(k3_tarski(sK5),sK5) != iProver_top ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_1980]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_16,plain,
% 1.68/0.98      ( r2_hidden(sK3(X0),X0) | v2_ordinal1(X0) ),
% 1.68/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1928,plain,
% 1.68/0.98      ( r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5))
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1942,plain,
% 1.68/0.98      ( r2_hidden(sK3(k3_tarski(sK5)),k3_tarski(sK5)) = iProver_top
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1928]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_15,plain,
% 1.68/0.98      ( r2_hidden(sK4(X0),X0) | v2_ordinal1(X0) ),
% 1.68/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1929,plain,
% 1.68/0.98      ( r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5))
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1940,plain,
% 1.68/0.98      ( r2_hidden(sK4(k3_tarski(sK5)),k3_tarski(sK5)) = iProver_top
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_14,plain,
% 1.68/0.98      ( ~ r2_hidden(sK3(X0),sK4(X0)) | v2_ordinal1(X0) ),
% 1.68/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1930,plain,
% 1.68/0.98      ( ~ r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5)))
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1938,plain,
% 1.68/0.98      ( r2_hidden(sK3(k3_tarski(sK5)),sK4(k3_tarski(sK5))) != iProver_top
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1930]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_13,plain,
% 1.68/0.98      ( v2_ordinal1(X0) | sK3(X0) != sK4(X0) ),
% 1.68/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1931,plain,
% 1.68/0.98      ( v2_ordinal1(k3_tarski(sK5))
% 1.68/0.98      | sK3(k3_tarski(sK5)) != sK4(k3_tarski(sK5)) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1936,plain,
% 1.68/0.98      ( sK3(k3_tarski(sK5)) != sK4(k3_tarski(sK5))
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1931]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_12,plain,
% 1.68/0.98      ( ~ r2_hidden(sK4(X0),sK3(X0)) | v2_ordinal1(X0) ),
% 1.68/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1932,plain,
% 1.68/0.98      ( ~ r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5)))
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1934,plain,
% 1.68/0.98      ( r2_hidden(sK4(k3_tarski(sK5)),sK3(k3_tarski(sK5))) != iProver_top
% 1.68/0.98      | v2_ordinal1(k3_tarski(sK5)) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1916,plain,
% 1.68/0.98      ( r2_hidden(sK2(k3_tarski(sK5)),X0)
% 1.68/0.98      | ~ r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5))
% 1.68/0.98      | ~ r1_tarski(k3_tarski(sK5),X0) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1920,plain,
% 1.68/0.98      ( r2_hidden(sK2(k3_tarski(sK5)),X0) = iProver_top
% 1.68/0.98      | r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
% 1.68/0.98      | r1_tarski(k3_tarski(sK5),X0) != iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1916]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1922,plain,
% 1.68/0.98      ( r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5)) != iProver_top
% 1.68/0.98      | r2_hidden(sK2(k3_tarski(sK5)),sK5) = iProver_top
% 1.68/0.98      | r1_tarski(k3_tarski(sK5),sK5) != iProver_top ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_1920]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_10,plain,
% 1.68/0.98      ( r2_hidden(sK2(X0),X0) | v1_ordinal1(X0) ),
% 1.68/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1892,plain,
% 1.68/0.98      ( r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5))
% 1.68/0.98      | v1_ordinal1(k3_tarski(sK5)) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1897,plain,
% 1.68/0.98      ( r2_hidden(sK2(k3_tarski(sK5)),k3_tarski(sK5)) = iProver_top
% 1.68/0.98      | v1_ordinal1(k3_tarski(sK5)) = iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_11,plain,
% 1.68/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 1.68/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1867,plain,
% 1.68/0.98      ( ~ r2_hidden(sK1(X0,X1),X1)
% 1.68/0.98      | r1_tarski(sK1(X0,X1),X1)
% 1.68/0.98      | ~ v1_ordinal1(X1) ),
% 1.68/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 1.68/0.98  
% 1.68/0.98  cnf(c_1868,plain,
% 1.68/0.98      ( r2_hidden(sK1(X0,X1),X1) != iProver_top
% 1.68/0.98      | r1_tarski(sK1(X0,X1),X1) = iProver_top
% 1.68/0.98      | v1_ordinal1(X1) != iProver_top ),
% 1.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1867]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1870,plain,
% 1.68/0.99      ( r2_hidden(sK1(sK5,sK5),sK5) != iProver_top
% 1.68/0.99      | r1_tarski(sK1(sK5,sK5),sK5) = iProver_top
% 1.68/0.99      | v1_ordinal1(sK5) != iProver_top ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_1868]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_18,plain,
% 1.68/0.99      ( ~ v1_ordinal1(X0) | v3_ordinal1(X0) | ~ v2_ordinal1(X0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1828,plain,
% 1.68/0.99      ( ~ v1_ordinal1(k3_tarski(sK5))
% 1.68/0.99      | v3_ordinal1(k3_tarski(sK5))
% 1.68/0.99      | ~ v2_ordinal1(k3_tarski(sK5)) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1829,plain,
% 1.68/0.99      ( v1_ordinal1(k3_tarski(sK5)) != iProver_top
% 1.68/0.99      | v3_ordinal1(k3_tarski(sK5)) = iProver_top
% 1.68/0.99      | v2_ordinal1(k3_tarski(sK5)) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1828]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_5,plain,
% 1.68/0.99      ( ~ r1_tarski(sK1(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 1.68/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_72,plain,
% 1.68/0.99      ( r1_tarski(sK1(X0,X1),X1) != iProver_top
% 1.68/0.99      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_74,plain,
% 1.68/0.99      ( r1_tarski(sK1(sK5,sK5),sK5) != iProver_top
% 1.68/0.99      | r1_tarski(k3_tarski(sK5),sK5) = iProver_top ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_72]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_6,plain,
% 1.68/0.99      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 1.68/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_69,plain,
% 1.68/0.99      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 1.68/0.99      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_71,plain,
% 1.68/0.99      ( r2_hidden(sK1(sK5,sK5),sK5) = iProver_top
% 1.68/0.99      | r1_tarski(k3_tarski(sK5),sK5) = iProver_top ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_69]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_19,plain,
% 1.68/0.99      ( ~ v3_ordinal1(X0) | v2_ordinal1(X0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_38,plain,
% 1.68/0.99      ( v3_ordinal1(X0) != iProver_top | v2_ordinal1(X0) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_40,plain,
% 1.68/0.99      ( v3_ordinal1(sK5) != iProver_top
% 1.68/0.99      | v2_ordinal1(sK5) = iProver_top ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_38]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_20,plain,
% 1.68/0.99      ( v1_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_35,plain,
% 1.68/0.99      ( v1_ordinal1(X0) = iProver_top | v3_ordinal1(X0) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_37,plain,
% 1.68/0.99      ( v1_ordinal1(sK5) = iProver_top
% 1.68/0.99      | v3_ordinal1(sK5) != iProver_top ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_35]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_24,negated_conjecture,
% 1.68/0.99      ( ~ v3_ordinal1(k3_tarski(sK5)) ),
% 1.68/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_27,plain,
% 1.68/0.99      ( v3_ordinal1(k3_tarski(sK5)) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_25,negated_conjecture,
% 1.68/0.99      ( v3_ordinal1(sK5) ),
% 1.68/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_26,plain,
% 1.68/0.99      ( v3_ordinal1(sK5) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(contradiction,plain,
% 1.68/0.99      ( $false ),
% 1.68/0.99      inference(minisat,
% 1.68/0.99                [status(thm)],
% 1.68/0.99                [c_2148,c_2135,c_2124,c_1982,c_1942,c_1940,c_1938,c_1936,
% 1.68/0.99                 c_1934,c_1922,c_1897,c_1870,c_1829,c_74,c_71,c_40,c_37,
% 1.68/0.99                 c_27,c_26]) ).
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.68/0.99  
% 1.68/0.99  ------                               Statistics
% 1.68/0.99  
% 1.68/0.99  ------ General
% 1.68/0.99  
% 1.68/0.99  abstr_ref_over_cycles:                  0
% 1.68/0.99  abstr_ref_under_cycles:                 0
% 1.68/0.99  gc_basic_clause_elim:                   0
% 1.68/0.99  forced_gc_time:                         0
% 1.68/0.99  parsing_time:                           0.009
% 1.68/0.99  unif_index_cands_time:                  0.
% 1.68/0.99  unif_index_add_time:                    0.
% 1.68/0.99  orderings_time:                         0.
% 1.68/0.99  out_proof_time:                         0.01
% 1.68/0.99  total_time:                             0.083
% 1.68/0.99  num_of_symbols:                         45
% 1.68/0.99  num_of_terms:                           973
% 1.68/0.99  
% 1.68/0.99  ------ Preprocessing
% 1.68/0.99  
% 1.68/0.99  num_of_splits:                          0
% 1.68/0.99  num_of_split_atoms:                     0
% 1.68/0.99  num_of_reused_defs:                     0
% 1.68/0.99  num_eq_ax_congr_red:                    35
% 1.68/0.99  num_of_sem_filtered_clauses:            1
% 1.68/0.99  num_of_subtypes:                        0
% 1.68/0.99  monotx_restored_types:                  0
% 1.68/0.99  sat_num_of_epr_types:                   0
% 1.68/0.99  sat_num_of_non_cyclic_types:            0
% 1.68/0.99  sat_guarded_non_collapsed_types:        0
% 1.68/0.99  num_pure_diseq_elim:                    0
% 1.68/0.99  simp_replaced_by:                       0
% 1.68/0.99  res_preprocessed:                       106
% 1.68/0.99  prep_upred:                             0
% 1.68/0.99  prep_unflattend:                        18
% 1.68/0.99  smt_new_axioms:                         0
% 1.68/0.99  pred_elim_cands:                        6
% 1.68/0.99  pred_elim:                              1
% 1.68/0.99  pred_elim_cl:                           1
% 1.68/0.99  pred_elim_cycles:                       5
% 1.68/0.99  merged_defs:                            0
% 1.68/0.99  merged_defs_ncl:                        0
% 1.68/0.99  bin_hyper_res:                          0
% 1.68/0.99  prep_cycles:                            4
% 1.68/0.99  pred_elim_time:                         0.01
% 1.68/0.99  splitting_time:                         0.
% 1.68/0.99  sem_filter_time:                        0.
% 1.68/0.99  monotx_time:                            0.
% 1.68/0.99  subtype_inf_time:                       0.
% 1.68/0.99  
% 1.68/0.99  ------ Problem properties
% 1.68/0.99  
% 1.68/0.99  clauses:                                23
% 1.68/0.99  conjectures:                            2
% 1.68/0.99  epr:                                    10
% 1.68/0.99  horn:                                   16
% 1.68/0.99  ground:                                 2
% 1.68/0.99  unary:                                  2
% 1.68/0.99  binary:                                 14
% 1.68/0.99  lits:                                   57
% 1.68/0.99  lits_eq:                                3
% 1.68/0.99  fd_pure:                                0
% 1.68/0.99  fd_pseudo:                              0
% 1.68/0.99  fd_cond:                                0
% 1.68/0.99  fd_pseudo_cond:                         2
% 1.68/0.99  ac_symbols:                             0
% 1.68/0.99  
% 1.68/0.99  ------ Propositional Solver
% 1.68/0.99  
% 1.68/0.99  prop_solver_calls:                      27
% 1.68/0.99  prop_fast_solver_calls:                 736
% 1.68/0.99  smt_solver_calls:                       0
% 1.68/0.99  smt_fast_solver_calls:                  0
% 1.68/0.99  prop_num_of_clauses:                    404
% 1.68/0.99  prop_preprocess_simplified:             4003
% 1.68/0.99  prop_fo_subsumed:                       0
% 1.68/0.99  prop_solver_time:                       0.
% 1.68/0.99  smt_solver_time:                        0.
% 1.68/0.99  smt_fast_solver_time:                   0.
% 1.68/0.99  prop_fast_solver_time:                  0.
% 1.68/0.99  prop_unsat_core_time:                   0.
% 1.68/0.99  
% 1.68/0.99  ------ QBF
% 1.68/0.99  
% 1.68/0.99  qbf_q_res:                              0
% 1.68/0.99  qbf_num_tautologies:                    0
% 1.68/0.99  qbf_prep_cycles:                        0
% 1.68/0.99  
% 1.68/0.99  ------ BMC1
% 1.68/0.99  
% 1.68/0.99  bmc1_current_bound:                     -1
% 1.68/0.99  bmc1_last_solved_bound:                 -1
% 1.68/0.99  bmc1_unsat_core_size:                   -1
% 1.68/0.99  bmc1_unsat_core_parents_size:           -1
% 1.68/0.99  bmc1_merge_next_fun:                    0
% 1.68/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.68/0.99  
% 1.68/0.99  ------ Instantiation
% 1.68/0.99  
% 1.68/0.99  inst_num_of_clauses:                    127
% 1.68/0.99  inst_num_in_passive:                    0
% 1.68/0.99  inst_num_in_active:                     85
% 1.68/0.99  inst_num_in_unprocessed:                42
% 1.68/0.99  inst_num_of_loops:                      109
% 1.68/0.99  inst_num_of_learning_restarts:          0
% 1.68/0.99  inst_num_moves_active_passive:          19
% 1.68/0.99  inst_lit_activity:                      0
% 1.68/0.99  inst_lit_activity_moves:                0
% 1.68/0.99  inst_num_tautologies:                   0
% 1.68/0.99  inst_num_prop_implied:                  0
% 1.68/0.99  inst_num_existing_simplified:           0
% 1.68/0.99  inst_num_eq_res_simplified:             0
% 1.68/0.99  inst_num_child_elim:                    0
% 1.68/0.99  inst_num_of_dismatching_blockings:      2
% 1.68/0.99  inst_num_of_non_proper_insts:           95
% 1.68/0.99  inst_num_of_duplicates:                 0
% 1.68/0.99  inst_inst_num_from_inst_to_res:         0
% 1.68/0.99  inst_dismatching_checking_time:         0.
% 1.68/0.99  
% 1.68/0.99  ------ Resolution
% 1.68/0.99  
% 1.68/0.99  res_num_of_clauses:                     0
% 1.68/0.99  res_num_in_passive:                     0
% 1.68/0.99  res_num_in_active:                      0
% 1.68/0.99  res_num_of_loops:                       110
% 1.68/0.99  res_forward_subset_subsumed:            28
% 1.68/0.99  res_backward_subset_subsumed:           0
% 1.68/0.99  res_forward_subsumed:                   0
% 1.68/0.99  res_backward_subsumed:                  0
% 1.68/0.99  res_forward_subsumption_resolution:     0
% 1.68/0.99  res_backward_subsumption_resolution:    0
% 1.68/0.99  res_clause_to_clause_subsumption:       68
% 1.68/0.99  res_orphan_elimination:                 0
% 1.68/0.99  res_tautology_del:                      12
% 1.68/0.99  res_num_eq_res_simplified:              0
% 1.68/0.99  res_num_sel_changes:                    0
% 1.68/0.99  res_moves_from_active_to_pass:          0
% 1.68/0.99  
% 1.68/0.99  ------ Superposition
% 1.68/0.99  
% 1.68/0.99  sup_time_total:                         0.
% 1.68/0.99  sup_time_generating:                    0.
% 1.68/0.99  sup_time_sim_full:                      0.
% 1.68/0.99  sup_time_sim_immed:                     0.
% 1.68/0.99  
% 1.68/0.99  sup_num_of_clauses:                     28
% 1.68/0.99  sup_num_in_active:                      20
% 1.68/0.99  sup_num_in_passive:                     8
% 1.68/0.99  sup_num_of_loops:                       20
% 1.68/0.99  sup_fw_superposition:                   7
% 1.68/0.99  sup_bw_superposition:                   1
% 1.68/0.99  sup_immediate_simplified:               4
% 1.68/0.99  sup_given_eliminated:                   0
% 1.68/0.99  comparisons_done:                       0
% 1.68/0.99  comparisons_avoided:                    0
% 1.68/0.99  
% 1.68/0.99  ------ Simplifications
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  sim_fw_subset_subsumed:                 2
% 1.68/0.99  sim_bw_subset_subsumed:                 0
% 1.68/0.99  sim_fw_subsumed:                        2
% 1.68/0.99  sim_bw_subsumed:                        0
% 1.68/0.99  sim_fw_subsumption_res:                 0
% 1.68/0.99  sim_bw_subsumption_res:                 0
% 1.68/0.99  sim_tautology_del:                      0
% 1.68/0.99  sim_eq_tautology_del:                   0
% 1.68/0.99  sim_eq_res_simp:                        0
% 1.68/0.99  sim_fw_demodulated:                     0
% 1.68/0.99  sim_bw_demodulated:                     0
% 1.68/0.99  sim_light_normalised:                   0
% 1.68/0.99  sim_joinable_taut:                      0
% 1.68/0.99  sim_joinable_simp:                      0
% 1.68/0.99  sim_ac_normalised:                      0
% 1.68/0.99  sim_smt_subsumption:                    0
% 1.68/0.99  
%------------------------------------------------------------------------------
