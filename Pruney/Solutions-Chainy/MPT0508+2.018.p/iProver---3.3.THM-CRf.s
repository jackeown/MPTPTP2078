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
% DateTime   : Thu Dec  3 11:45:10 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 231 expanded)
%              Number of clauses        :   58 (  84 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  242 ( 817 expanded)
%              Number of equality atoms :   64 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(sK3,X1))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21,f20])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_437,plain,
    ( r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8562,plain,
    ( r1_tarski(k7_relat_1(sK2,sK1),k7_relat_1(sK3,sK1))
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_318,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_325,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_323,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_816,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_325,c_323])).

cnf(c_22,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_28,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_417,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(k7_relat_1(X0,X1))
    | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_418,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1854,plain,
    ( v1_relat_1(X0) != iProver_top
    | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_816,c_22,c_28,c_418])).

cnf(c_1855,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1854])).

cnf(c_1864,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0),X0) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_318,c_1855])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_321,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_328,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_826,plain,
    ( r1_tarski(X0,sK1) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_321,c_328])).

cnf(c_964,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_325,c_826])).

cnf(c_1999,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_964])).

cnf(c_11,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_405,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_475,plain,
    ( r1_tarski(k1_relat_1(X0),sK1)
    | ~ r1_tarski(k1_relat_1(X0),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_552,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_554,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_556,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_553,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_558,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_560,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_2676,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1999,c_11,c_14,c_556,c_560])).

cnf(c_2682,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0)
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_323])).

cnf(c_555,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_559,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_476,plain,
    ( ~ r1_tarski(k1_relat_1(X0),sK1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_929,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(X0,sK0))
    | k7_relat_1(k7_relat_1(X0,sK0),sK1) = k7_relat_1(X0,sK0) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_931,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_1721,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1723,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_5445,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2682,c_10,c_7,c_555,c_559,c_931,c_1723])).

cnf(c_326,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5448,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),X0) != iProver_top
    | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5445,c_326])).

cnf(c_5491,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
    | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5448])).

cnf(c_5493,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5491])).

cnf(c_525,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,X1))
    | ~ r1_tarski(X0,k7_relat_1(sK2,X1))
    | ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK3,X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2830,plain,
    ( r1_tarski(k7_relat_1(X0,X1),k7_relat_1(sK3,X2))
    | ~ r1_tarski(k7_relat_1(X0,X1),k7_relat_1(sK2,X2))
    | ~ r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2)) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_3863,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK1),k7_relat_1(sK3,sK1))
    | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2830])).

cnf(c_4,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3415,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8562,c_5493,c_3863,c_3415,c_1723,c_6,c_8,c_9,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:38:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.92/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/0.95  
% 2.92/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.95  
% 2.92/0.95  ------  iProver source info
% 2.92/0.95  
% 2.92/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.95  git: non_committed_changes: false
% 2.92/0.95  git: last_make_outside_of_git: false
% 2.92/0.95  
% 2.92/0.95  ------ 
% 2.92/0.95  
% 2.92/0.95  ------ Input Options
% 2.92/0.95  
% 2.92/0.95  --out_options                           all
% 2.92/0.95  --tptp_safe_out                         true
% 2.92/0.95  --problem_path                          ""
% 2.92/0.95  --include_path                          ""
% 2.92/0.95  --clausifier                            res/vclausify_rel
% 2.92/0.95  --clausifier_options                    --mode clausify
% 2.92/0.95  --stdin                                 false
% 2.92/0.95  --stats_out                             all
% 2.92/0.95  
% 2.92/0.95  ------ General Options
% 2.92/0.95  
% 2.92/0.95  --fof                                   false
% 2.92/0.95  --time_out_real                         305.
% 2.92/0.95  --time_out_virtual                      -1.
% 2.92/0.95  --symbol_type_check                     false
% 2.92/0.95  --clausify_out                          false
% 2.92/0.95  --sig_cnt_out                           false
% 2.92/0.95  --trig_cnt_out                          false
% 2.92/0.95  --trig_cnt_out_tolerance                1.
% 2.92/0.95  --trig_cnt_out_sk_spl                   false
% 2.92/0.95  --abstr_cl_out                          false
% 2.92/0.95  
% 2.92/0.95  ------ Global Options
% 2.92/0.95  
% 2.92/0.95  --schedule                              default
% 2.92/0.95  --add_important_lit                     false
% 2.92/0.95  --prop_solver_per_cl                    1000
% 2.92/0.95  --min_unsat_core                        false
% 2.92/0.95  --soft_assumptions                      false
% 2.92/0.95  --soft_lemma_size                       3
% 2.92/0.95  --prop_impl_unit_size                   0
% 2.92/0.95  --prop_impl_unit                        []
% 2.92/0.95  --share_sel_clauses                     true
% 2.92/0.95  --reset_solvers                         false
% 2.92/0.95  --bc_imp_inh                            [conj_cone]
% 2.92/0.95  --conj_cone_tolerance                   3.
% 2.92/0.95  --extra_neg_conj                        none
% 2.92/0.95  --large_theory_mode                     true
% 2.92/0.95  --prolific_symb_bound                   200
% 2.92/0.95  --lt_threshold                          2000
% 2.92/0.95  --clause_weak_htbl                      true
% 2.92/0.95  --gc_record_bc_elim                     false
% 2.92/0.95  
% 2.92/0.95  ------ Preprocessing Options
% 2.92/0.95  
% 2.92/0.95  --preprocessing_flag                    true
% 2.92/0.95  --time_out_prep_mult                    0.1
% 2.92/0.95  --splitting_mode                        input
% 2.92/0.95  --splitting_grd                         true
% 2.92/0.95  --splitting_cvd                         false
% 2.92/0.95  --splitting_cvd_svl                     false
% 2.92/0.95  --splitting_nvd                         32
% 2.92/0.95  --sub_typing                            true
% 2.92/0.95  --prep_gs_sim                           true
% 2.92/0.95  --prep_unflatten                        true
% 2.92/0.95  --prep_res_sim                          true
% 2.92/0.95  --prep_upred                            true
% 2.92/0.95  --prep_sem_filter                       exhaustive
% 2.92/0.95  --prep_sem_filter_out                   false
% 2.92/0.95  --pred_elim                             true
% 2.92/0.95  --res_sim_input                         true
% 2.92/0.95  --eq_ax_congr_red                       true
% 2.92/0.95  --pure_diseq_elim                       true
% 2.92/0.95  --brand_transform                       false
% 2.92/0.95  --non_eq_to_eq                          false
% 2.92/0.95  --prep_def_merge                        true
% 2.92/0.95  --prep_def_merge_prop_impl              false
% 2.92/0.95  --prep_def_merge_mbd                    true
% 2.92/0.95  --prep_def_merge_tr_red                 false
% 2.92/0.95  --prep_def_merge_tr_cl                  false
% 2.92/0.95  --smt_preprocessing                     true
% 2.92/0.95  --smt_ac_axioms                         fast
% 2.92/0.95  --preprocessed_out                      false
% 2.92/0.95  --preprocessed_stats                    false
% 2.92/0.95  
% 2.92/0.95  ------ Abstraction refinement Options
% 2.92/0.95  
% 2.92/0.95  --abstr_ref                             []
% 2.92/0.95  --abstr_ref_prep                        false
% 2.92/0.95  --abstr_ref_until_sat                   false
% 2.92/0.95  --abstr_ref_sig_restrict                funpre
% 2.92/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.95  --abstr_ref_under                       []
% 2.92/0.95  
% 2.92/0.95  ------ SAT Options
% 2.92/0.95  
% 2.92/0.95  --sat_mode                              false
% 2.92/0.95  --sat_fm_restart_options                ""
% 2.92/0.95  --sat_gr_def                            false
% 2.92/0.95  --sat_epr_types                         true
% 2.92/0.95  --sat_non_cyclic_types                  false
% 2.92/0.95  --sat_finite_models                     false
% 2.92/0.95  --sat_fm_lemmas                         false
% 2.92/0.95  --sat_fm_prep                           false
% 2.92/0.95  --sat_fm_uc_incr                        true
% 2.92/0.95  --sat_out_model                         small
% 2.92/0.95  --sat_out_clauses                       false
% 2.92/0.95  
% 2.92/0.95  ------ QBF Options
% 2.92/0.95  
% 2.92/0.95  --qbf_mode                              false
% 2.92/0.95  --qbf_elim_univ                         false
% 2.92/0.95  --qbf_dom_inst                          none
% 2.92/0.95  --qbf_dom_pre_inst                      false
% 2.92/0.95  --qbf_sk_in                             false
% 2.92/0.95  --qbf_pred_elim                         true
% 2.92/0.95  --qbf_split                             512
% 2.92/0.95  
% 2.92/0.95  ------ BMC1 Options
% 2.92/0.95  
% 2.92/0.95  --bmc1_incremental                      false
% 2.92/0.95  --bmc1_axioms                           reachable_all
% 2.92/0.95  --bmc1_min_bound                        0
% 2.92/0.95  --bmc1_max_bound                        -1
% 2.92/0.95  --bmc1_max_bound_default                -1
% 2.92/0.95  --bmc1_symbol_reachability              true
% 2.92/0.95  --bmc1_property_lemmas                  false
% 2.92/0.95  --bmc1_k_induction                      false
% 2.92/0.95  --bmc1_non_equiv_states                 false
% 2.92/0.95  --bmc1_deadlock                         false
% 2.92/0.95  --bmc1_ucm                              false
% 2.92/0.95  --bmc1_add_unsat_core                   none
% 2.92/0.95  --bmc1_unsat_core_children              false
% 2.92/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.95  --bmc1_out_stat                         full
% 2.92/0.95  --bmc1_ground_init                      false
% 2.92/0.95  --bmc1_pre_inst_next_state              false
% 2.92/0.95  --bmc1_pre_inst_state                   false
% 2.92/0.95  --bmc1_pre_inst_reach_state             false
% 2.92/0.95  --bmc1_out_unsat_core                   false
% 2.92/0.95  --bmc1_aig_witness_out                  false
% 2.92/0.95  --bmc1_verbose                          false
% 2.92/0.95  --bmc1_dump_clauses_tptp                false
% 2.92/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.95  --bmc1_dump_file                        -
% 2.92/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.95  --bmc1_ucm_extend_mode                  1
% 2.92/0.95  --bmc1_ucm_init_mode                    2
% 2.92/0.95  --bmc1_ucm_cone_mode                    none
% 2.92/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.95  --bmc1_ucm_relax_model                  4
% 2.92/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.95  --bmc1_ucm_layered_model                none
% 2.92/0.95  --bmc1_ucm_max_lemma_size               10
% 2.92/0.95  
% 2.92/0.95  ------ AIG Options
% 2.92/0.95  
% 2.92/0.95  --aig_mode                              false
% 2.92/0.95  
% 2.92/0.95  ------ Instantiation Options
% 2.92/0.95  
% 2.92/0.95  --instantiation_flag                    true
% 2.92/0.95  --inst_sos_flag                         false
% 2.92/0.95  --inst_sos_phase                        true
% 2.92/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.95  --inst_lit_sel_side                     num_symb
% 2.92/0.95  --inst_solver_per_active                1400
% 2.92/0.95  --inst_solver_calls_frac                1.
% 2.92/0.95  --inst_passive_queue_type               priority_queues
% 2.92/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.95  --inst_passive_queues_freq              [25;2]
% 2.92/0.95  --inst_dismatching                      true
% 2.92/0.95  --inst_eager_unprocessed_to_passive     true
% 2.92/0.95  --inst_prop_sim_given                   true
% 2.92/0.95  --inst_prop_sim_new                     false
% 2.92/0.95  --inst_subs_new                         false
% 2.92/0.95  --inst_eq_res_simp                      false
% 2.92/0.95  --inst_subs_given                       false
% 2.92/0.95  --inst_orphan_elimination               true
% 2.92/0.95  --inst_learning_loop_flag               true
% 2.92/0.95  --inst_learning_start                   3000
% 2.92/0.95  --inst_learning_factor                  2
% 2.92/0.95  --inst_start_prop_sim_after_learn       3
% 2.92/0.95  --inst_sel_renew                        solver
% 2.92/0.95  --inst_lit_activity_flag                true
% 2.92/0.95  --inst_restr_to_given                   false
% 2.92/0.95  --inst_activity_threshold               500
% 2.92/0.95  --inst_out_proof                        true
% 2.92/0.95  
% 2.92/0.95  ------ Resolution Options
% 2.92/0.95  
% 2.92/0.95  --resolution_flag                       true
% 2.92/0.95  --res_lit_sel                           adaptive
% 2.92/0.95  --res_lit_sel_side                      none
% 2.92/0.95  --res_ordering                          kbo
% 2.92/0.95  --res_to_prop_solver                    active
% 2.92/0.95  --res_prop_simpl_new                    false
% 2.92/0.95  --res_prop_simpl_given                  true
% 2.92/0.95  --res_passive_queue_type                priority_queues
% 2.92/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.95  --res_passive_queues_freq               [15;5]
% 2.92/0.95  --res_forward_subs                      full
% 2.92/0.95  --res_backward_subs                     full
% 2.92/0.95  --res_forward_subs_resolution           true
% 2.92/0.95  --res_backward_subs_resolution          true
% 2.92/0.95  --res_orphan_elimination                true
% 2.92/0.95  --res_time_limit                        2.
% 2.92/0.95  --res_out_proof                         true
% 2.92/0.95  
% 2.92/0.95  ------ Superposition Options
% 2.92/0.95  
% 2.92/0.95  --superposition_flag                    true
% 2.92/0.95  --sup_passive_queue_type                priority_queues
% 2.92/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.95  --demod_completeness_check              fast
% 2.92/0.95  --demod_use_ground                      true
% 2.92/0.95  --sup_to_prop_solver                    passive
% 2.92/0.95  --sup_prop_simpl_new                    true
% 2.92/0.95  --sup_prop_simpl_given                  true
% 2.92/0.95  --sup_fun_splitting                     false
% 2.92/0.95  --sup_smt_interval                      50000
% 2.92/0.95  
% 2.92/0.95  ------ Superposition Simplification Setup
% 2.92/0.95  
% 2.92/0.95  --sup_indices_passive                   []
% 2.92/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.95  --sup_full_bw                           [BwDemod]
% 2.92/0.95  --sup_immed_triv                        [TrivRules]
% 2.92/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.95  --sup_immed_bw_main                     []
% 2.92/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.95  
% 2.92/0.95  ------ Combination Options
% 2.92/0.95  
% 2.92/0.95  --comb_res_mult                         3
% 2.92/0.95  --comb_sup_mult                         2
% 2.92/0.95  --comb_inst_mult                        10
% 2.92/0.95  
% 2.92/0.95  ------ Debug Options
% 2.92/0.95  
% 2.92/0.95  --dbg_backtrace                         false
% 2.92/0.95  --dbg_dump_prop_clauses                 false
% 2.92/0.95  --dbg_dump_prop_clauses_file            -
% 2.92/0.95  --dbg_out_stat                          false
% 2.92/0.95  ------ Parsing...
% 2.92/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/0.95  
% 2.92/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.92/0.95  
% 2.92/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/0.95  
% 2.92/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/0.95  ------ Proving...
% 2.92/0.95  ------ Problem Properties 
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  clauses                                 11
% 2.92/0.95  conjectures                             5
% 2.92/0.95  EPR                                     5
% 2.92/0.95  Horn                                    11
% 2.92/0.95  unary                                   5
% 2.92/0.95  binary                                  3
% 2.92/0.95  lits                                    21
% 2.92/0.95  lits eq                                 1
% 2.92/0.95  fd_pure                                 0
% 2.92/0.95  fd_pseudo                               0
% 2.92/0.95  fd_cond                                 0
% 2.92/0.95  fd_pseudo_cond                          0
% 2.92/0.95  AC symbols                              0
% 2.92/0.95  
% 2.92/0.95  ------ Schedule dynamic 5 is on 
% 2.92/0.95  
% 2.92/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  ------ 
% 2.92/0.95  Current options:
% 2.92/0.95  ------ 
% 2.92/0.95  
% 2.92/0.95  ------ Input Options
% 2.92/0.95  
% 2.92/0.95  --out_options                           all
% 2.92/0.95  --tptp_safe_out                         true
% 2.92/0.95  --problem_path                          ""
% 2.92/0.95  --include_path                          ""
% 2.92/0.95  --clausifier                            res/vclausify_rel
% 2.92/0.95  --clausifier_options                    --mode clausify
% 2.92/0.95  --stdin                                 false
% 2.92/0.95  --stats_out                             all
% 2.92/0.95  
% 2.92/0.95  ------ General Options
% 2.92/0.95  
% 2.92/0.95  --fof                                   false
% 2.92/0.95  --time_out_real                         305.
% 2.92/0.95  --time_out_virtual                      -1.
% 2.92/0.95  --symbol_type_check                     false
% 2.92/0.95  --clausify_out                          false
% 2.92/0.95  --sig_cnt_out                           false
% 2.92/0.95  --trig_cnt_out                          false
% 2.92/0.95  --trig_cnt_out_tolerance                1.
% 2.92/0.95  --trig_cnt_out_sk_spl                   false
% 2.92/0.95  --abstr_cl_out                          false
% 2.92/0.95  
% 2.92/0.95  ------ Global Options
% 2.92/0.95  
% 2.92/0.95  --schedule                              default
% 2.92/0.95  --add_important_lit                     false
% 2.92/0.95  --prop_solver_per_cl                    1000
% 2.92/0.95  --min_unsat_core                        false
% 2.92/0.95  --soft_assumptions                      false
% 2.92/0.95  --soft_lemma_size                       3
% 2.92/0.95  --prop_impl_unit_size                   0
% 2.92/0.95  --prop_impl_unit                        []
% 2.92/0.95  --share_sel_clauses                     true
% 2.92/0.95  --reset_solvers                         false
% 2.92/0.95  --bc_imp_inh                            [conj_cone]
% 2.92/0.95  --conj_cone_tolerance                   3.
% 2.92/0.95  --extra_neg_conj                        none
% 2.92/0.95  --large_theory_mode                     true
% 2.92/0.95  --prolific_symb_bound                   200
% 2.92/0.95  --lt_threshold                          2000
% 2.92/0.95  --clause_weak_htbl                      true
% 2.92/0.95  --gc_record_bc_elim                     false
% 2.92/0.95  
% 2.92/0.95  ------ Preprocessing Options
% 2.92/0.95  
% 2.92/0.95  --preprocessing_flag                    true
% 2.92/0.95  --time_out_prep_mult                    0.1
% 2.92/0.95  --splitting_mode                        input
% 2.92/0.95  --splitting_grd                         true
% 2.92/0.95  --splitting_cvd                         false
% 2.92/0.95  --splitting_cvd_svl                     false
% 2.92/0.95  --splitting_nvd                         32
% 2.92/0.95  --sub_typing                            true
% 2.92/0.95  --prep_gs_sim                           true
% 2.92/0.95  --prep_unflatten                        true
% 2.92/0.95  --prep_res_sim                          true
% 2.92/0.95  --prep_upred                            true
% 2.92/0.95  --prep_sem_filter                       exhaustive
% 2.92/0.95  --prep_sem_filter_out                   false
% 2.92/0.95  --pred_elim                             true
% 2.92/0.95  --res_sim_input                         true
% 2.92/0.95  --eq_ax_congr_red                       true
% 2.92/0.95  --pure_diseq_elim                       true
% 2.92/0.95  --brand_transform                       false
% 2.92/0.95  --non_eq_to_eq                          false
% 2.92/0.95  --prep_def_merge                        true
% 2.92/0.95  --prep_def_merge_prop_impl              false
% 2.92/0.95  --prep_def_merge_mbd                    true
% 2.92/0.95  --prep_def_merge_tr_red                 false
% 2.92/0.95  --prep_def_merge_tr_cl                  false
% 2.92/0.95  --smt_preprocessing                     true
% 2.92/0.95  --smt_ac_axioms                         fast
% 2.92/0.95  --preprocessed_out                      false
% 2.92/0.95  --preprocessed_stats                    false
% 2.92/0.95  
% 2.92/0.95  ------ Abstraction refinement Options
% 2.92/0.95  
% 2.92/0.95  --abstr_ref                             []
% 2.92/0.95  --abstr_ref_prep                        false
% 2.92/0.95  --abstr_ref_until_sat                   false
% 2.92/0.95  --abstr_ref_sig_restrict                funpre
% 2.92/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.95  --abstr_ref_under                       []
% 2.92/0.95  
% 2.92/0.95  ------ SAT Options
% 2.92/0.95  
% 2.92/0.95  --sat_mode                              false
% 2.92/0.95  --sat_fm_restart_options                ""
% 2.92/0.95  --sat_gr_def                            false
% 2.92/0.95  --sat_epr_types                         true
% 2.92/0.95  --sat_non_cyclic_types                  false
% 2.92/0.95  --sat_finite_models                     false
% 2.92/0.95  --sat_fm_lemmas                         false
% 2.92/0.95  --sat_fm_prep                           false
% 2.92/0.95  --sat_fm_uc_incr                        true
% 2.92/0.95  --sat_out_model                         small
% 2.92/0.95  --sat_out_clauses                       false
% 2.92/0.95  
% 2.92/0.95  ------ QBF Options
% 2.92/0.95  
% 2.92/0.95  --qbf_mode                              false
% 2.92/0.95  --qbf_elim_univ                         false
% 2.92/0.95  --qbf_dom_inst                          none
% 2.92/0.95  --qbf_dom_pre_inst                      false
% 2.92/0.95  --qbf_sk_in                             false
% 2.92/0.95  --qbf_pred_elim                         true
% 2.92/0.95  --qbf_split                             512
% 2.92/0.95  
% 2.92/0.95  ------ BMC1 Options
% 2.92/0.95  
% 2.92/0.95  --bmc1_incremental                      false
% 2.92/0.95  --bmc1_axioms                           reachable_all
% 2.92/0.95  --bmc1_min_bound                        0
% 2.92/0.95  --bmc1_max_bound                        -1
% 2.92/0.95  --bmc1_max_bound_default                -1
% 2.92/0.95  --bmc1_symbol_reachability              true
% 2.92/0.95  --bmc1_property_lemmas                  false
% 2.92/0.95  --bmc1_k_induction                      false
% 2.92/0.95  --bmc1_non_equiv_states                 false
% 2.92/0.95  --bmc1_deadlock                         false
% 2.92/0.95  --bmc1_ucm                              false
% 2.92/0.95  --bmc1_add_unsat_core                   none
% 2.92/0.95  --bmc1_unsat_core_children              false
% 2.92/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.95  --bmc1_out_stat                         full
% 2.92/0.95  --bmc1_ground_init                      false
% 2.92/0.95  --bmc1_pre_inst_next_state              false
% 2.92/0.95  --bmc1_pre_inst_state                   false
% 2.92/0.95  --bmc1_pre_inst_reach_state             false
% 2.92/0.95  --bmc1_out_unsat_core                   false
% 2.92/0.95  --bmc1_aig_witness_out                  false
% 2.92/0.95  --bmc1_verbose                          false
% 2.92/0.95  --bmc1_dump_clauses_tptp                false
% 2.92/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.95  --bmc1_dump_file                        -
% 2.92/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.95  --bmc1_ucm_extend_mode                  1
% 2.92/0.95  --bmc1_ucm_init_mode                    2
% 2.92/0.95  --bmc1_ucm_cone_mode                    none
% 2.92/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.95  --bmc1_ucm_relax_model                  4
% 2.92/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.95  --bmc1_ucm_layered_model                none
% 2.92/0.95  --bmc1_ucm_max_lemma_size               10
% 2.92/0.95  
% 2.92/0.95  ------ AIG Options
% 2.92/0.95  
% 2.92/0.95  --aig_mode                              false
% 2.92/0.95  
% 2.92/0.95  ------ Instantiation Options
% 2.92/0.95  
% 2.92/0.95  --instantiation_flag                    true
% 2.92/0.95  --inst_sos_flag                         false
% 2.92/0.95  --inst_sos_phase                        true
% 2.92/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.95  --inst_lit_sel_side                     none
% 2.92/0.95  --inst_solver_per_active                1400
% 2.92/0.95  --inst_solver_calls_frac                1.
% 2.92/0.95  --inst_passive_queue_type               priority_queues
% 2.92/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.95  --inst_passive_queues_freq              [25;2]
% 2.92/0.95  --inst_dismatching                      true
% 2.92/0.95  --inst_eager_unprocessed_to_passive     true
% 2.92/0.95  --inst_prop_sim_given                   true
% 2.92/0.95  --inst_prop_sim_new                     false
% 2.92/0.95  --inst_subs_new                         false
% 2.92/0.95  --inst_eq_res_simp                      false
% 2.92/0.95  --inst_subs_given                       false
% 2.92/0.95  --inst_orphan_elimination               true
% 2.92/0.95  --inst_learning_loop_flag               true
% 2.92/0.95  --inst_learning_start                   3000
% 2.92/0.95  --inst_learning_factor                  2
% 2.92/0.95  --inst_start_prop_sim_after_learn       3
% 2.92/0.95  --inst_sel_renew                        solver
% 2.92/0.95  --inst_lit_activity_flag                true
% 2.92/0.95  --inst_restr_to_given                   false
% 2.92/0.95  --inst_activity_threshold               500
% 2.92/0.95  --inst_out_proof                        true
% 2.92/0.95  
% 2.92/0.95  ------ Resolution Options
% 2.92/0.95  
% 2.92/0.95  --resolution_flag                       false
% 2.92/0.95  --res_lit_sel                           adaptive
% 2.92/0.95  --res_lit_sel_side                      none
% 2.92/0.95  --res_ordering                          kbo
% 2.92/0.95  --res_to_prop_solver                    active
% 2.92/0.95  --res_prop_simpl_new                    false
% 2.92/0.95  --res_prop_simpl_given                  true
% 2.92/0.95  --res_passive_queue_type                priority_queues
% 2.92/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.95  --res_passive_queues_freq               [15;5]
% 2.92/0.95  --res_forward_subs                      full
% 2.92/0.95  --res_backward_subs                     full
% 2.92/0.95  --res_forward_subs_resolution           true
% 2.92/0.95  --res_backward_subs_resolution          true
% 2.92/0.95  --res_orphan_elimination                true
% 2.92/0.95  --res_time_limit                        2.
% 2.92/0.95  --res_out_proof                         true
% 2.92/0.95  
% 2.92/0.95  ------ Superposition Options
% 2.92/0.95  
% 2.92/0.95  --superposition_flag                    true
% 2.92/0.95  --sup_passive_queue_type                priority_queues
% 2.92/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.95  --demod_completeness_check              fast
% 2.92/0.95  --demod_use_ground                      true
% 2.92/0.95  --sup_to_prop_solver                    passive
% 2.92/0.95  --sup_prop_simpl_new                    true
% 2.92/0.95  --sup_prop_simpl_given                  true
% 2.92/0.95  --sup_fun_splitting                     false
% 2.92/0.95  --sup_smt_interval                      50000
% 2.92/0.95  
% 2.92/0.95  ------ Superposition Simplification Setup
% 2.92/0.95  
% 2.92/0.95  --sup_indices_passive                   []
% 2.92/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.95  --sup_full_bw                           [BwDemod]
% 2.92/0.95  --sup_immed_triv                        [TrivRules]
% 2.92/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.95  --sup_immed_bw_main                     []
% 2.92/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.95  
% 2.92/0.95  ------ Combination Options
% 2.92/0.95  
% 2.92/0.95  --comb_res_mult                         3
% 2.92/0.95  --comb_sup_mult                         2
% 2.92/0.95  --comb_inst_mult                        10
% 2.92/0.95  
% 2.92/0.95  ------ Debug Options
% 2.92/0.95  
% 2.92/0.95  --dbg_backtrace                         false
% 2.92/0.95  --dbg_dump_prop_clauses                 false
% 2.92/0.95  --dbg_dump_prop_clauses_file            -
% 2.92/0.95  --dbg_out_stat                          false
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  ------ Proving...
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  % SZS status Theorem for theBenchmark.p
% 2.92/0.95  
% 2.92/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/0.95  
% 2.92/0.95  fof(f3,axiom,(
% 2.92/0.95    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 2.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.95  
% 2.92/0.95  fof(f12,plain,(
% 2.92/0.95    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.92/0.95    inference(ennf_transformation,[],[f3])).
% 2.92/0.95  
% 2.92/0.95  fof(f13,plain,(
% 2.92/0.95    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.92/0.95    inference(flattening,[],[f12])).
% 2.92/0.95  
% 2.92/0.95  fof(f25,plain,(
% 2.92/0.95    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.92/0.95    inference(cnf_transformation,[],[f13])).
% 2.92/0.95  
% 2.92/0.95  fof(f7,conjecture,(
% 2.92/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 2.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.95  
% 2.92/0.95  fof(f8,negated_conjecture,(
% 2.92/0.95    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 2.92/0.95    inference(negated_conjecture,[],[f7])).
% 2.92/0.95  
% 2.92/0.95  fof(f18,plain,(
% 2.92/0.95    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 2.92/0.95    inference(ennf_transformation,[],[f8])).
% 2.92/0.95  
% 2.92/0.95  fof(f19,plain,(
% 2.92/0.95    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 2.92/0.95    inference(flattening,[],[f18])).
% 2.92/0.95  
% 2.92/0.95  fof(f21,plain,(
% 2.92/0.95    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(sK3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,sK3) & v1_relat_1(sK3))) )),
% 2.92/0.95    introduced(choice_axiom,[])).
% 2.92/0.95  
% 2.92/0.95  fof(f20,plain,(
% 2.92/0.95    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 2.92/0.95    introduced(choice_axiom,[])).
% 2.92/0.95  
% 2.92/0.95  fof(f22,plain,(
% 2.92/0.95    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 2.92/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21,f20])).
% 2.92/0.95  
% 2.92/0.95  fof(f29,plain,(
% 2.92/0.95    v1_relat_1(sK2)),
% 2.92/0.95    inference(cnf_transformation,[],[f22])).
% 2.92/0.95  
% 2.92/0.95  fof(f4,axiom,(
% 2.92/0.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.95  
% 2.92/0.95  fof(f14,plain,(
% 2.92/0.95    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.92/0.95    inference(ennf_transformation,[],[f4])).
% 2.92/0.95  
% 2.92/0.95  fof(f26,plain,(
% 2.92/0.95    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.92/0.95    inference(cnf_transformation,[],[f14])).
% 2.92/0.95  
% 2.92/0.95  fof(f6,axiom,(
% 2.92/0.95    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.95  
% 2.92/0.95  fof(f16,plain,(
% 2.92/0.95    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.92/0.95    inference(ennf_transformation,[],[f6])).
% 2.92/0.95  
% 2.92/0.95  fof(f17,plain,(
% 2.92/0.95    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.92/0.95    inference(flattening,[],[f16])).
% 2.92/0.95  
% 2.92/0.95  fof(f28,plain,(
% 2.92/0.95    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.92/0.95    inference(cnf_transformation,[],[f17])).
% 2.92/0.95  
% 2.92/0.95  fof(f2,axiom,(
% 2.92/0.95    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.95  
% 2.92/0.95  fof(f11,plain,(
% 2.92/0.95    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.92/0.95    inference(ennf_transformation,[],[f2])).
% 2.92/0.95  
% 2.92/0.95  fof(f24,plain,(
% 2.92/0.95    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.92/0.95    inference(cnf_transformation,[],[f11])).
% 2.92/0.95  
% 2.92/0.95  fof(f32,plain,(
% 2.92/0.95    r1_tarski(sK0,sK1)),
% 2.92/0.95    inference(cnf_transformation,[],[f22])).
% 2.92/0.95  
% 2.92/0.95  fof(f1,axiom,(
% 2.92/0.95    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.95  
% 2.92/0.95  fof(f9,plain,(
% 2.92/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.92/0.95    inference(ennf_transformation,[],[f1])).
% 2.92/0.95  
% 2.92/0.95  fof(f10,plain,(
% 2.92/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.92/0.95    inference(flattening,[],[f9])).
% 2.92/0.95  
% 2.92/0.95  fof(f23,plain,(
% 2.92/0.95    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.92/0.95    inference(cnf_transformation,[],[f10])).
% 2.92/0.95  
% 2.92/0.95  fof(f5,axiom,(
% 2.92/0.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/0.95  
% 2.92/0.95  fof(f15,plain,(
% 2.92/0.95    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.92/0.95    inference(ennf_transformation,[],[f5])).
% 2.92/0.95  
% 2.92/0.95  fof(f27,plain,(
% 2.92/0.95    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.92/0.95    inference(cnf_transformation,[],[f15])).
% 2.92/0.95  
% 2.92/0.95  fof(f33,plain,(
% 2.92/0.95    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 2.92/0.95    inference(cnf_transformation,[],[f22])).
% 2.92/0.95  
% 2.92/0.95  fof(f31,plain,(
% 2.92/0.95    r1_tarski(sK2,sK3)),
% 2.92/0.95    inference(cnf_transformation,[],[f22])).
% 2.92/0.95  
% 2.92/0.95  fof(f30,plain,(
% 2.92/0.95    v1_relat_1(sK3)),
% 2.92/0.95    inference(cnf_transformation,[],[f22])).
% 2.92/0.95  
% 2.92/0.95  cnf(c_2,plain,
% 2.92/0.95      ( ~ r1_tarski(X0,X1)
% 2.92/0.95      | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
% 2.92/0.95      | ~ v1_relat_1(X1)
% 2.92/0.95      | ~ v1_relat_1(X0) ),
% 2.92/0.95      inference(cnf_transformation,[],[f25]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_437,plain,
% 2.92/0.95      ( r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))
% 2.92/0.95      | ~ r1_tarski(sK2,sK3)
% 2.92/0.95      | ~ v1_relat_1(sK3)
% 2.92/0.95      | ~ v1_relat_1(sK2) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_2]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_8562,plain,
% 2.92/0.95      ( r1_tarski(k7_relat_1(sK2,sK1),k7_relat_1(sK3,sK1))
% 2.92/0.95      | ~ r1_tarski(sK2,sK3)
% 2.92/0.95      | ~ v1_relat_1(sK3)
% 2.92/0.95      | ~ v1_relat_1(sK2) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_437]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_10,negated_conjecture,
% 2.92/0.95      ( v1_relat_1(sK2) ),
% 2.92/0.95      inference(cnf_transformation,[],[f29]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_318,plain,
% 2.92/0.95      ( v1_relat_1(sK2) = iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_3,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.92/0.95      inference(cnf_transformation,[],[f26]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_325,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 2.92/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_5,plain,
% 2.92/0.95      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.92/0.95      | ~ v1_relat_1(X0)
% 2.92/0.95      | k7_relat_1(X0,X1) = X0 ),
% 2.92/0.95      inference(cnf_transformation,[],[f28]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_323,plain,
% 2.92/0.95      ( k7_relat_1(X0,X1) = X0
% 2.92/0.95      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.92/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_816,plain,
% 2.92/0.95      ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
% 2.92/0.95      | v1_relat_1(X0) != iProver_top
% 2.92/0.95      | v1_relat_1(k7_relat_1(X0,X1)) != iProver_top ),
% 2.92/0.95      inference(superposition,[status(thm)],[c_325,c_323]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_22,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 2.92/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_1,plain,
% 2.92/0.95      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.92/0.95      inference(cnf_transformation,[],[f24]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_28,plain,
% 2.92/0.95      ( v1_relat_1(X0) != iProver_top
% 2.92/0.95      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_417,plain,
% 2.92/0.95      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
% 2.92/0.95      | ~ v1_relat_1(k7_relat_1(X0,X1))
% 2.92/0.95      | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_5]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_418,plain,
% 2.92/0.95      ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
% 2.92/0.95      | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) != iProver_top
% 2.92/0.95      | v1_relat_1(k7_relat_1(X0,X1)) != iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_1854,plain,
% 2.92/0.95      ( v1_relat_1(X0) != iProver_top
% 2.92/0.95      | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
% 2.92/0.95      inference(global_propositional_subsumption,
% 2.92/0.95                [status(thm)],
% 2.92/0.95                [c_816,c_22,c_28,c_418]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_1855,plain,
% 2.92/0.95      ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
% 2.92/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.95      inference(renaming,[status(thm)],[c_1854]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_1864,plain,
% 2.92/0.95      ( k7_relat_1(k7_relat_1(sK2,X0),X0) = k7_relat_1(sK2,X0) ),
% 2.92/0.95      inference(superposition,[status(thm)],[c_318,c_1855]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_7,negated_conjecture,
% 2.92/0.95      ( r1_tarski(sK0,sK1) ),
% 2.92/0.95      inference(cnf_transformation,[],[f32]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_321,plain,
% 2.92/0.95      ( r1_tarski(sK0,sK1) = iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_0,plain,
% 2.92/0.95      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.92/0.95      inference(cnf_transformation,[],[f23]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_328,plain,
% 2.92/0.95      ( r1_tarski(X0,X1) != iProver_top
% 2.92/0.95      | r1_tarski(X2,X0) != iProver_top
% 2.92/0.95      | r1_tarski(X2,X1) = iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_826,plain,
% 2.92/0.95      ( r1_tarski(X0,sK1) = iProver_top
% 2.92/0.95      | r1_tarski(X0,sK0) != iProver_top ),
% 2.92/0.95      inference(superposition,[status(thm)],[c_321,c_328]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_964,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1) = iProver_top
% 2.92/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.95      inference(superposition,[status(thm)],[c_325,c_826]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_1999,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) = iProver_top
% 2.92/0.95      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 2.92/0.95      inference(superposition,[status(thm)],[c_1864,c_964]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_11,plain,
% 2.92/0.95      ( v1_relat_1(sK2) = iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_14,plain,
% 2.92/0.95      ( r1_tarski(sK0,sK1) = iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_405,plain,
% 2.92/0.95      ( r1_tarski(X0,sK1) | ~ r1_tarski(X0,sK0) | ~ r1_tarski(sK0,sK1) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_0]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_475,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(X0),sK1)
% 2.92/0.95      | ~ r1_tarski(k1_relat_1(X0),sK0)
% 2.92/0.95      | ~ r1_tarski(sK0,sK1) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_405]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_552,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1)
% 2.92/0.95      | ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
% 2.92/0.95      | ~ r1_tarski(sK0,sK1) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_475]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_554,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1) = iProver_top
% 2.92/0.95      | r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) != iProver_top
% 2.92/0.95      | r1_tarski(sK0,sK1) != iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_556,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) = iProver_top
% 2.92/0.95      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) != iProver_top
% 2.92/0.95      | r1_tarski(sK0,sK1) != iProver_top ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_554]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_553,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
% 2.92/0.95      | ~ v1_relat_1(X0) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_3]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_558,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) = iProver_top
% 2.92/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_560,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0) = iProver_top
% 2.92/0.95      | v1_relat_1(sK2) != iProver_top ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_558]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_2676,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) = iProver_top ),
% 2.92/0.95      inference(global_propositional_subsumption,
% 2.92/0.95                [status(thm)],
% 2.92/0.95                [c_1999,c_11,c_14,c_556,c_560]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_2682,plain,
% 2.92/0.95      ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0)
% 2.92/0.95      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 2.92/0.95      inference(superposition,[status(thm)],[c_2676,c_323]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_555,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
% 2.92/0.95      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0)
% 2.92/0.95      | ~ r1_tarski(sK0,sK1) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_552]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_559,plain,
% 2.92/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK0)
% 2.92/0.95      | ~ v1_relat_1(sK2) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_553]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_476,plain,
% 2.92/0.95      ( ~ r1_tarski(k1_relat_1(X0),sK1)
% 2.92/0.95      | ~ v1_relat_1(X0)
% 2.92/0.95      | k7_relat_1(X0,sK1) = X0 ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_5]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_929,plain,
% 2.92/0.95      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK1)
% 2.92/0.95      | ~ v1_relat_1(k7_relat_1(X0,sK0))
% 2.92/0.95      | k7_relat_1(k7_relat_1(X0,sK0),sK1) = k7_relat_1(X0,sK0) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_476]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_931,plain,
% 2.92/0.95      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
% 2.92/0.95      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
% 2.92/0.95      | k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_929]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_1721,plain,
% 2.92/0.95      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,sK0)) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_1723,plain,
% 2.92/0.95      ( v1_relat_1(k7_relat_1(sK2,sK0)) | ~ v1_relat_1(sK2) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_1721]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_5445,plain,
% 2.92/0.95      ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0) ),
% 2.92/0.95      inference(global_propositional_subsumption,
% 2.92/0.95                [status(thm)],
% 2.92/0.95                [c_2682,c_10,c_7,c_555,c_559,c_931,c_1723]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_326,plain,
% 2.92/0.95      ( r1_tarski(X0,X1) != iProver_top
% 2.92/0.95      | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2)) = iProver_top
% 2.92/0.95      | v1_relat_1(X0) != iProver_top
% 2.92/0.95      | v1_relat_1(X1) != iProver_top ),
% 2.92/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_5448,plain,
% 2.92/0.95      ( r1_tarski(k7_relat_1(sK2,sK0),X0) != iProver_top
% 2.92/0.95      | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1)) = iProver_top
% 2.92/0.95      | v1_relat_1(X0) != iProver_top
% 2.92/0.95      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 2.92/0.95      inference(superposition,[status(thm)],[c_5445,c_326]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_5491,plain,
% 2.92/0.95      ( ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
% 2.92/0.95      | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1))
% 2.92/0.95      | ~ v1_relat_1(X0)
% 2.92/0.95      | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
% 2.92/0.95      inference(predicate_to_equality_rev,[status(thm)],[c_5448]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_5493,plain,
% 2.92/0.95      ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
% 2.92/0.95      | ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
% 2.92/0.95      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
% 2.92/0.95      | ~ v1_relat_1(sK2) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_5491]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_525,plain,
% 2.92/0.95      ( r1_tarski(X0,k7_relat_1(sK3,X1))
% 2.92/0.95      | ~ r1_tarski(X0,k7_relat_1(sK2,X1))
% 2.92/0.95      | ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK3,X1)) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_0]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_2830,plain,
% 2.92/0.95      ( r1_tarski(k7_relat_1(X0,X1),k7_relat_1(sK3,X2))
% 2.92/0.95      | ~ r1_tarski(k7_relat_1(X0,X1),k7_relat_1(sK2,X2))
% 2.92/0.95      | ~ r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK3,X2)) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_525]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_3863,plain,
% 2.92/0.95      ( ~ r1_tarski(k7_relat_1(sK2,sK1),k7_relat_1(sK3,sK1))
% 2.92/0.95      | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
% 2.92/0.95      | ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_2830]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_4,plain,
% 2.92/0.95      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 2.92/0.95      inference(cnf_transformation,[],[f27]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_3415,plain,
% 2.92/0.95      ( r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~ v1_relat_1(sK2) ),
% 2.92/0.95      inference(instantiation,[status(thm)],[c_4]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_6,negated_conjecture,
% 2.92/0.95      ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
% 2.92/0.95      inference(cnf_transformation,[],[f33]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_8,negated_conjecture,
% 2.92/0.95      ( r1_tarski(sK2,sK3) ),
% 2.92/0.95      inference(cnf_transformation,[],[f31]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(c_9,negated_conjecture,
% 2.92/0.95      ( v1_relat_1(sK3) ),
% 2.92/0.95      inference(cnf_transformation,[],[f30]) ).
% 2.92/0.95  
% 2.92/0.95  cnf(contradiction,plain,
% 2.92/0.95      ( $false ),
% 2.92/0.95      inference(minisat,
% 2.92/0.95                [status(thm)],
% 2.92/0.95                [c_8562,c_5493,c_3863,c_3415,c_1723,c_6,c_8,c_9,c_10]) ).
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/0.95  
% 2.92/0.95  ------                               Statistics
% 2.92/0.95  
% 2.92/0.95  ------ General
% 2.92/0.95  
% 2.92/0.95  abstr_ref_over_cycles:                  0
% 2.92/0.95  abstr_ref_under_cycles:                 0
% 2.92/0.95  gc_basic_clause_elim:                   0
% 2.92/0.95  forced_gc_time:                         0
% 2.92/0.95  parsing_time:                           0.007
% 2.92/0.95  unif_index_cands_time:                  0.
% 2.92/0.95  unif_index_add_time:                    0.
% 2.92/0.95  orderings_time:                         0.
% 2.92/0.95  out_proof_time:                         0.008
% 2.92/0.95  total_time:                             0.263
% 2.92/0.95  num_of_symbols:                         39
% 2.92/0.95  num_of_terms:                           11579
% 2.92/0.95  
% 2.92/0.95  ------ Preprocessing
% 2.92/0.95  
% 2.92/0.95  num_of_splits:                          0
% 2.92/0.95  num_of_split_atoms:                     0
% 2.92/0.95  num_of_reused_defs:                     0
% 2.92/0.95  num_eq_ax_congr_red:                    0
% 2.92/0.95  num_of_sem_filtered_clauses:            1
% 2.92/0.95  num_of_subtypes:                        1
% 2.92/0.95  monotx_restored_types:                  0
% 2.92/0.95  sat_num_of_epr_types:                   0
% 2.92/0.95  sat_num_of_non_cyclic_types:            0
% 2.92/0.95  sat_guarded_non_collapsed_types:        1
% 2.92/0.95  num_pure_diseq_elim:                    0
% 2.92/0.95  simp_replaced_by:                       0
% 2.92/0.95  res_preprocessed:                       46
% 2.92/0.95  prep_upred:                             0
% 2.92/0.95  prep_unflattend:                        0
% 2.92/0.95  smt_new_axioms:                         0
% 2.92/0.95  pred_elim_cands:                        2
% 2.92/0.95  pred_elim:                              0
% 2.92/0.95  pred_elim_cl:                           0
% 2.92/0.95  pred_elim_cycles:                       1
% 2.92/0.95  merged_defs:                            0
% 2.92/0.95  merged_defs_ncl:                        0
% 2.92/0.95  bin_hyper_res:                          0
% 2.92/0.95  prep_cycles:                            3
% 2.92/0.95  pred_elim_time:                         0.
% 2.92/0.95  splitting_time:                         0.
% 2.92/0.95  sem_filter_time:                        0.
% 2.92/0.95  monotx_time:                            0.
% 2.92/0.95  subtype_inf_time:                       0.
% 2.92/0.95  
% 2.92/0.95  ------ Problem properties
% 2.92/0.95  
% 2.92/0.95  clauses:                                11
% 2.92/0.95  conjectures:                            5
% 2.92/0.95  epr:                                    5
% 2.92/0.95  horn:                                   11
% 2.92/0.95  ground:                                 5
% 2.92/0.95  unary:                                  5
% 2.92/0.95  binary:                                 3
% 2.92/0.95  lits:                                   21
% 2.92/0.95  lits_eq:                                1
% 2.92/0.95  fd_pure:                                0
% 2.92/0.95  fd_pseudo:                              0
% 2.92/0.95  fd_cond:                                0
% 2.92/0.95  fd_pseudo_cond:                         0
% 2.92/0.95  ac_symbols:                             0
% 2.92/0.95  
% 2.92/0.95  ------ Propositional Solver
% 2.92/0.95  
% 2.92/0.95  prop_solver_calls:                      23
% 2.92/0.95  prop_fast_solver_calls:                 351
% 2.92/0.95  smt_solver_calls:                       0
% 2.92/0.95  smt_fast_solver_calls:                  0
% 2.92/0.95  prop_num_of_clauses:                    3122
% 2.92/0.95  prop_preprocess_simplified:             7113
% 2.92/0.95  prop_fo_subsumed:                       12
% 2.92/0.95  prop_solver_time:                       0.
% 2.92/0.95  smt_solver_time:                        0.
% 2.92/0.95  smt_fast_solver_time:                   0.
% 2.92/0.95  prop_fast_solver_time:                  0.
% 2.92/0.95  prop_unsat_core_time:                   0.
% 2.92/0.95  
% 2.92/0.95  ------ QBF
% 2.92/0.95  
% 2.92/0.95  qbf_q_res:                              0
% 2.92/0.95  qbf_num_tautologies:                    0
% 2.92/0.95  qbf_prep_cycles:                        0
% 2.92/0.95  
% 2.92/0.95  ------ BMC1
% 2.92/0.95  
% 2.92/0.95  bmc1_current_bound:                     -1
% 2.92/0.95  bmc1_last_solved_bound:                 -1
% 2.92/0.95  bmc1_unsat_core_size:                   -1
% 2.92/0.95  bmc1_unsat_core_parents_size:           -1
% 2.92/0.95  bmc1_merge_next_fun:                    0
% 2.92/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.92/0.95  
% 2.92/0.95  ------ Instantiation
% 2.92/0.95  
% 2.92/0.95  inst_num_of_clauses:                    735
% 2.92/0.95  inst_num_in_passive:                    408
% 2.92/0.95  inst_num_in_active:                     326
% 2.92/0.95  inst_num_in_unprocessed:                0
% 2.92/0.95  inst_num_of_loops:                      350
% 2.92/0.95  inst_num_of_learning_restarts:          0
% 2.92/0.95  inst_num_moves_active_passive:          22
% 2.92/0.95  inst_lit_activity:                      0
% 2.92/0.95  inst_lit_activity_moves:                0
% 2.92/0.95  inst_num_tautologies:                   0
% 2.92/0.95  inst_num_prop_implied:                  0
% 2.92/0.95  inst_num_existing_simplified:           0
% 2.92/0.95  inst_num_eq_res_simplified:             0
% 2.92/0.95  inst_num_child_elim:                    0
% 2.92/0.95  inst_num_of_dismatching_blockings:      994
% 2.92/0.95  inst_num_of_non_proper_insts:           918
% 2.92/0.95  inst_num_of_duplicates:                 0
% 2.92/0.95  inst_inst_num_from_inst_to_res:         0
% 2.92/0.95  inst_dismatching_checking_time:         0.
% 2.92/0.95  
% 2.92/0.95  ------ Resolution
% 2.92/0.95  
% 2.92/0.95  res_num_of_clauses:                     0
% 2.92/0.95  res_num_in_passive:                     0
% 2.92/0.95  res_num_in_active:                      0
% 2.92/0.95  res_num_of_loops:                       49
% 2.92/0.95  res_forward_subset_subsumed:            21
% 2.92/0.95  res_backward_subset_subsumed:           0
% 2.92/0.95  res_forward_subsumed:                   0
% 2.92/0.95  res_backward_subsumed:                  0
% 2.92/0.95  res_forward_subsumption_resolution:     0
% 2.92/0.95  res_backward_subsumption_resolution:    0
% 2.92/0.95  res_clause_to_clause_subsumption:       1254
% 2.92/0.95  res_orphan_elimination:                 0
% 2.92/0.95  res_tautology_del:                      133
% 2.92/0.95  res_num_eq_res_simplified:              0
% 2.92/0.95  res_num_sel_changes:                    0
% 2.92/0.95  res_moves_from_active_to_pass:          0
% 2.92/0.95  
% 2.92/0.95  ------ Superposition
% 2.92/0.95  
% 2.92/0.95  sup_time_total:                         0.
% 2.92/0.95  sup_time_generating:                    0.
% 2.92/0.95  sup_time_sim_full:                      0.
% 2.92/0.95  sup_time_sim_immed:                     0.
% 2.92/0.95  
% 2.92/0.95  sup_num_of_clauses:                     239
% 2.92/0.95  sup_num_in_active:                      68
% 2.92/0.95  sup_num_in_passive:                     171
% 2.92/0.95  sup_num_of_loops:                       68
% 2.92/0.95  sup_fw_superposition:                   112
% 2.92/0.95  sup_bw_superposition:                   230
% 2.92/0.95  sup_immediate_simplified:               34
% 2.92/0.95  sup_given_eliminated:                   0
% 2.92/0.95  comparisons_done:                       0
% 2.92/0.95  comparisons_avoided:                    0
% 2.92/0.95  
% 2.92/0.95  ------ Simplifications
% 2.92/0.95  
% 2.92/0.95  
% 2.92/0.95  sim_fw_subset_subsumed:                 15
% 2.92/0.95  sim_bw_subset_subsumed:                 7
% 2.92/0.95  sim_fw_subsumed:                        19
% 2.92/0.95  sim_bw_subsumed:                        0
% 2.92/0.95  sim_fw_subsumption_res:                 0
% 2.92/0.95  sim_bw_subsumption_res:                 0
% 2.92/0.95  sim_tautology_del:                      40
% 2.92/0.95  sim_eq_tautology_del:                   0
% 2.92/0.95  sim_eq_res_simp:                        0
% 2.92/0.95  sim_fw_demodulated:                     0
% 2.92/0.95  sim_bw_demodulated:                     0
% 2.92/0.95  sim_light_normalised:                   0
% 2.92/0.95  sim_joinable_taut:                      0
% 2.92/0.95  sim_joinable_simp:                      0
% 2.92/0.95  sim_ac_normalised:                      0
% 2.92/0.95  sim_smt_subsumption:                    0
% 2.92/0.95  
%------------------------------------------------------------------------------
