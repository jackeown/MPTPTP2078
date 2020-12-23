%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:47 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 270 expanded)
%              Number of clauses        :   57 (  78 expanded)
%              Number of leaves         :   12 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  293 (1557 expanded)
%              Number of equality atoms :  139 ( 628 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k1_relat_1(X1) = k2_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0))
        & k1_relat_1(sK1) = k2_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k1_relat_1(X1) = k2_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    & k1_relat_1(sK1) = k2_relat_1(sK0)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_710,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_708,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_709,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_713,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_717,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2710,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_713,c_717])).

cnf(c_12950,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_2710])).

cnf(c_25,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19719,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12950,c_25])).

cnf(c_19720,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_19719])).

cnf(c_19730,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_19720])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_338,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_339,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_34,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_341,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_24,c_23,c_20,c_34])).

cnf(c_19,negated_conjecture,
    ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_747,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_341,c_19])).

cnf(c_19752,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19730,c_747])).

cnf(c_20171,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_710,c_19752])).

cnf(c_18,negated_conjecture,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_715,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1641,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_713,c_715])).

cnf(c_5016,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_1641])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_354,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_355,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_40,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_357,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_24,c_23,c_20,c_40])).

cnf(c_5019,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5016,c_357])).

cnf(c_5245,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5019,c_25])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_712,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1445,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_712,c_715])).

cnf(c_5,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1454,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_1445,c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_718,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2422,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_718])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2448,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2422,c_6])).

cnf(c_42,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2873,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2448,c_42])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_716,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2880,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2873,c_716])).

cnf(c_6293,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_710,c_2880])).

cnf(c_20189,plain,
    ( k2_funct_1(sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_20171,c_18,c_5245,c_6293])).

cnf(c_17,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20189,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:33:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.58/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.99  
% 3.58/0.99  ------  iProver source info
% 3.58/0.99  
% 3.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.99  git: non_committed_changes: false
% 3.58/0.99  git: last_make_outside_of_git: false
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  
% 3.58/0.99  ------ Input Options
% 3.58/0.99  
% 3.58/0.99  --out_options                           all
% 3.58/0.99  --tptp_safe_out                         true
% 3.58/0.99  --problem_path                          ""
% 3.58/0.99  --include_path                          ""
% 3.58/0.99  --clausifier                            res/vclausify_rel
% 3.58/0.99  --clausifier_options                    --mode clausify
% 3.58/0.99  --stdin                                 false
% 3.58/0.99  --stats_out                             all
% 3.58/0.99  
% 3.58/0.99  ------ General Options
% 3.58/0.99  
% 3.58/0.99  --fof                                   false
% 3.58/0.99  --time_out_real                         305.
% 3.58/0.99  --time_out_virtual                      -1.
% 3.58/0.99  --symbol_type_check                     false
% 3.58/0.99  --clausify_out                          false
% 3.58/0.99  --sig_cnt_out                           false
% 3.58/0.99  --trig_cnt_out                          false
% 3.58/0.99  --trig_cnt_out_tolerance                1.
% 3.58/0.99  --trig_cnt_out_sk_spl                   false
% 3.58/0.99  --abstr_cl_out                          false
% 3.58/0.99  
% 3.58/0.99  ------ Global Options
% 3.58/0.99  
% 3.58/0.99  --schedule                              default
% 3.58/0.99  --add_important_lit                     false
% 3.58/0.99  --prop_solver_per_cl                    1000
% 3.58/0.99  --min_unsat_core                        false
% 3.58/0.99  --soft_assumptions                      false
% 3.58/0.99  --soft_lemma_size                       3
% 3.58/0.99  --prop_impl_unit_size                   0
% 3.58/0.99  --prop_impl_unit                        []
% 3.58/0.99  --share_sel_clauses                     true
% 3.58/0.99  --reset_solvers                         false
% 3.58/0.99  --bc_imp_inh                            [conj_cone]
% 3.58/0.99  --conj_cone_tolerance                   3.
% 3.58/0.99  --extra_neg_conj                        none
% 3.58/0.99  --large_theory_mode                     true
% 3.58/0.99  --prolific_symb_bound                   200
% 3.58/0.99  --lt_threshold                          2000
% 3.58/0.99  --clause_weak_htbl                      true
% 3.58/0.99  --gc_record_bc_elim                     false
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing Options
% 3.58/0.99  
% 3.58/0.99  --preprocessing_flag                    true
% 3.58/0.99  --time_out_prep_mult                    0.1
% 3.58/0.99  --splitting_mode                        input
% 3.58/0.99  --splitting_grd                         true
% 3.58/0.99  --splitting_cvd                         false
% 3.58/0.99  --splitting_cvd_svl                     false
% 3.58/0.99  --splitting_nvd                         32
% 3.58/0.99  --sub_typing                            true
% 3.58/0.99  --prep_gs_sim                           true
% 3.58/0.99  --prep_unflatten                        true
% 3.58/0.99  --prep_res_sim                          true
% 3.58/0.99  --prep_upred                            true
% 3.58/0.99  --prep_sem_filter                       exhaustive
% 3.58/0.99  --prep_sem_filter_out                   false
% 3.58/0.99  --pred_elim                             true
% 3.58/0.99  --res_sim_input                         true
% 3.58/0.99  --eq_ax_congr_red                       true
% 3.58/0.99  --pure_diseq_elim                       true
% 3.58/0.99  --brand_transform                       false
% 3.58/0.99  --non_eq_to_eq                          false
% 3.58/0.99  --prep_def_merge                        true
% 3.58/0.99  --prep_def_merge_prop_impl              false
% 3.58/0.99  --prep_def_merge_mbd                    true
% 3.58/0.99  --prep_def_merge_tr_red                 false
% 3.58/0.99  --prep_def_merge_tr_cl                  false
% 3.58/0.99  --smt_preprocessing                     true
% 3.58/0.99  --smt_ac_axioms                         fast
% 3.58/0.99  --preprocessed_out                      false
% 3.58/0.99  --preprocessed_stats                    false
% 3.58/0.99  
% 3.58/0.99  ------ Abstraction refinement Options
% 3.58/0.99  
% 3.58/0.99  --abstr_ref                             []
% 3.58/0.99  --abstr_ref_prep                        false
% 3.58/0.99  --abstr_ref_until_sat                   false
% 3.58/0.99  --abstr_ref_sig_restrict                funpre
% 3.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/0.99  --abstr_ref_under                       []
% 3.58/0.99  
% 3.58/0.99  ------ SAT Options
% 3.58/0.99  
% 3.58/0.99  --sat_mode                              false
% 3.58/0.99  --sat_fm_restart_options                ""
% 3.58/0.99  --sat_gr_def                            false
% 3.58/0.99  --sat_epr_types                         true
% 3.58/0.99  --sat_non_cyclic_types                  false
% 3.58/0.99  --sat_finite_models                     false
% 3.58/0.99  --sat_fm_lemmas                         false
% 3.58/0.99  --sat_fm_prep                           false
% 3.58/0.99  --sat_fm_uc_incr                        true
% 3.58/0.99  --sat_out_model                         small
% 3.58/0.99  --sat_out_clauses                       false
% 3.58/0.99  
% 3.58/0.99  ------ QBF Options
% 3.58/0.99  
% 3.58/0.99  --qbf_mode                              false
% 3.58/0.99  --qbf_elim_univ                         false
% 3.58/0.99  --qbf_dom_inst                          none
% 3.58/0.99  --qbf_dom_pre_inst                      false
% 3.58/0.99  --qbf_sk_in                             false
% 3.58/0.99  --qbf_pred_elim                         true
% 3.58/0.99  --qbf_split                             512
% 3.58/0.99  
% 3.58/0.99  ------ BMC1 Options
% 3.58/0.99  
% 3.58/0.99  --bmc1_incremental                      false
% 3.58/0.99  --bmc1_axioms                           reachable_all
% 3.58/0.99  --bmc1_min_bound                        0
% 3.58/0.99  --bmc1_max_bound                        -1
% 3.58/0.99  --bmc1_max_bound_default                -1
% 3.58/0.99  --bmc1_symbol_reachability              true
% 3.58/0.99  --bmc1_property_lemmas                  false
% 3.58/0.99  --bmc1_k_induction                      false
% 3.58/0.99  --bmc1_non_equiv_states                 false
% 3.58/0.99  --bmc1_deadlock                         false
% 3.58/0.99  --bmc1_ucm                              false
% 3.58/0.99  --bmc1_add_unsat_core                   none
% 3.58/1.00  --bmc1_unsat_core_children              false
% 3.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/1.00  --bmc1_out_stat                         full
% 3.58/1.00  --bmc1_ground_init                      false
% 3.58/1.00  --bmc1_pre_inst_next_state              false
% 3.58/1.00  --bmc1_pre_inst_state                   false
% 3.58/1.00  --bmc1_pre_inst_reach_state             false
% 3.58/1.00  --bmc1_out_unsat_core                   false
% 3.58/1.00  --bmc1_aig_witness_out                  false
% 3.58/1.00  --bmc1_verbose                          false
% 3.58/1.00  --bmc1_dump_clauses_tptp                false
% 3.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.58/1.00  --bmc1_dump_file                        -
% 3.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.58/1.00  --bmc1_ucm_extend_mode                  1
% 3.58/1.00  --bmc1_ucm_init_mode                    2
% 3.58/1.00  --bmc1_ucm_cone_mode                    none
% 3.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.58/1.00  --bmc1_ucm_relax_model                  4
% 3.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/1.00  --bmc1_ucm_layered_model                none
% 3.58/1.00  --bmc1_ucm_max_lemma_size               10
% 3.58/1.00  
% 3.58/1.00  ------ AIG Options
% 3.58/1.00  
% 3.58/1.00  --aig_mode                              false
% 3.58/1.00  
% 3.58/1.00  ------ Instantiation Options
% 3.58/1.00  
% 3.58/1.00  --instantiation_flag                    true
% 3.58/1.00  --inst_sos_flag                         false
% 3.58/1.00  --inst_sos_phase                        true
% 3.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/1.00  --inst_lit_sel_side                     num_symb
% 3.58/1.00  --inst_solver_per_active                1400
% 3.58/1.00  --inst_solver_calls_frac                1.
% 3.58/1.00  --inst_passive_queue_type               priority_queues
% 3.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/1.00  --inst_passive_queues_freq              [25;2]
% 3.58/1.00  --inst_dismatching                      true
% 3.58/1.00  --inst_eager_unprocessed_to_passive     true
% 3.58/1.00  --inst_prop_sim_given                   true
% 3.58/1.00  --inst_prop_sim_new                     false
% 3.58/1.00  --inst_subs_new                         false
% 3.58/1.00  --inst_eq_res_simp                      false
% 3.58/1.00  --inst_subs_given                       false
% 3.58/1.00  --inst_orphan_elimination               true
% 3.58/1.00  --inst_learning_loop_flag               true
% 3.58/1.00  --inst_learning_start                   3000
% 3.58/1.00  --inst_learning_factor                  2
% 3.58/1.00  --inst_start_prop_sim_after_learn       3
% 3.58/1.00  --inst_sel_renew                        solver
% 3.58/1.00  --inst_lit_activity_flag                true
% 3.58/1.00  --inst_restr_to_given                   false
% 3.58/1.00  --inst_activity_threshold               500
% 3.58/1.00  --inst_out_proof                        true
% 3.58/1.00  
% 3.58/1.00  ------ Resolution Options
% 3.58/1.00  
% 3.58/1.00  --resolution_flag                       true
% 3.58/1.00  --res_lit_sel                           adaptive
% 3.58/1.00  --res_lit_sel_side                      none
% 3.58/1.00  --res_ordering                          kbo
% 3.58/1.00  --res_to_prop_solver                    active
% 3.58/1.00  --res_prop_simpl_new                    false
% 3.58/1.00  --res_prop_simpl_given                  true
% 3.58/1.00  --res_passive_queue_type                priority_queues
% 3.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/1.00  --res_passive_queues_freq               [15;5]
% 3.58/1.00  --res_forward_subs                      full
% 3.58/1.00  --res_backward_subs                     full
% 3.58/1.00  --res_forward_subs_resolution           true
% 3.58/1.00  --res_backward_subs_resolution          true
% 3.58/1.00  --res_orphan_elimination                true
% 3.58/1.00  --res_time_limit                        2.
% 3.58/1.00  --res_out_proof                         true
% 3.58/1.00  
% 3.58/1.00  ------ Superposition Options
% 3.58/1.00  
% 3.58/1.00  --superposition_flag                    true
% 3.58/1.00  --sup_passive_queue_type                priority_queues
% 3.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.58/1.00  --demod_completeness_check              fast
% 3.58/1.00  --demod_use_ground                      true
% 3.58/1.00  --sup_to_prop_solver                    passive
% 3.58/1.00  --sup_prop_simpl_new                    true
% 3.58/1.00  --sup_prop_simpl_given                  true
% 3.58/1.00  --sup_fun_splitting                     false
% 3.58/1.00  --sup_smt_interval                      50000
% 3.58/1.00  
% 3.58/1.00  ------ Superposition Simplification Setup
% 3.58/1.00  
% 3.58/1.00  --sup_indices_passive                   []
% 3.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/1.00  --sup_full_bw                           [BwDemod]
% 3.58/1.00  --sup_immed_triv                        [TrivRules]
% 3.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/1.00  --sup_immed_bw_main                     []
% 3.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/1.00  
% 3.58/1.00  ------ Combination Options
% 3.58/1.00  
% 3.58/1.00  --comb_res_mult                         3
% 3.58/1.00  --comb_sup_mult                         2
% 3.58/1.00  --comb_inst_mult                        10
% 3.58/1.00  
% 3.58/1.00  ------ Debug Options
% 3.58/1.00  
% 3.58/1.00  --dbg_backtrace                         false
% 3.58/1.00  --dbg_dump_prop_clauses                 false
% 3.58/1.00  --dbg_dump_prop_clauses_file            -
% 3.58/1.00  --dbg_out_stat                          false
% 3.58/1.00  ------ Parsing...
% 3.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/1.00  
% 3.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.58/1.00  
% 3.58/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/1.00  
% 3.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/1.00  ------ Proving...
% 3.58/1.00  ------ Problem Properties 
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  clauses                                 27
% 3.58/1.00  conjectures                             7
% 3.58/1.00  EPR                                     4
% 3.58/1.00  Horn                                    27
% 3.58/1.00  unary                                   14
% 3.58/1.00  binary                                  6
% 3.58/1.00  lits                                    48
% 3.58/1.00  lits eq                                 18
% 3.58/1.00  fd_pure                                 0
% 3.58/1.00  fd_pseudo                               0
% 3.58/1.00  fd_cond                                 0
% 3.58/1.00  fd_pseudo_cond                          0
% 3.58/1.00  AC symbols                              0
% 3.58/1.00  
% 3.58/1.00  ------ Schedule dynamic 5 is on 
% 3.58/1.00  
% 3.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  ------ 
% 3.58/1.00  Current options:
% 3.58/1.00  ------ 
% 3.58/1.00  
% 3.58/1.00  ------ Input Options
% 3.58/1.00  
% 3.58/1.00  --out_options                           all
% 3.58/1.00  --tptp_safe_out                         true
% 3.58/1.00  --problem_path                          ""
% 3.58/1.00  --include_path                          ""
% 3.58/1.00  --clausifier                            res/vclausify_rel
% 3.58/1.00  --clausifier_options                    --mode clausify
% 3.58/1.00  --stdin                                 false
% 3.58/1.00  --stats_out                             all
% 3.58/1.00  
% 3.58/1.00  ------ General Options
% 3.58/1.00  
% 3.58/1.00  --fof                                   false
% 3.58/1.00  --time_out_real                         305.
% 3.58/1.00  --time_out_virtual                      -1.
% 3.58/1.00  --symbol_type_check                     false
% 3.58/1.00  --clausify_out                          false
% 3.58/1.00  --sig_cnt_out                           false
% 3.58/1.00  --trig_cnt_out                          false
% 3.58/1.00  --trig_cnt_out_tolerance                1.
% 3.58/1.00  --trig_cnt_out_sk_spl                   false
% 3.58/1.00  --abstr_cl_out                          false
% 3.58/1.00  
% 3.58/1.00  ------ Global Options
% 3.58/1.00  
% 3.58/1.00  --schedule                              default
% 3.58/1.00  --add_important_lit                     false
% 3.58/1.00  --prop_solver_per_cl                    1000
% 3.58/1.00  --min_unsat_core                        false
% 3.58/1.00  --soft_assumptions                      false
% 3.58/1.00  --soft_lemma_size                       3
% 3.58/1.00  --prop_impl_unit_size                   0
% 3.58/1.00  --prop_impl_unit                        []
% 3.58/1.00  --share_sel_clauses                     true
% 3.58/1.00  --reset_solvers                         false
% 3.58/1.00  --bc_imp_inh                            [conj_cone]
% 3.58/1.00  --conj_cone_tolerance                   3.
% 3.58/1.00  --extra_neg_conj                        none
% 3.58/1.00  --large_theory_mode                     true
% 3.58/1.00  --prolific_symb_bound                   200
% 3.58/1.00  --lt_threshold                          2000
% 3.58/1.00  --clause_weak_htbl                      true
% 3.58/1.00  --gc_record_bc_elim                     false
% 3.58/1.00  
% 3.58/1.00  ------ Preprocessing Options
% 3.58/1.00  
% 3.58/1.00  --preprocessing_flag                    true
% 3.58/1.00  --time_out_prep_mult                    0.1
% 3.58/1.00  --splitting_mode                        input
% 3.58/1.00  --splitting_grd                         true
% 3.58/1.00  --splitting_cvd                         false
% 3.58/1.00  --splitting_cvd_svl                     false
% 3.58/1.00  --splitting_nvd                         32
% 3.58/1.00  --sub_typing                            true
% 3.58/1.00  --prep_gs_sim                           true
% 3.58/1.00  --prep_unflatten                        true
% 3.58/1.00  --prep_res_sim                          true
% 3.58/1.00  --prep_upred                            true
% 3.58/1.00  --prep_sem_filter                       exhaustive
% 3.58/1.00  --prep_sem_filter_out                   false
% 3.58/1.00  --pred_elim                             true
% 3.58/1.00  --res_sim_input                         true
% 3.58/1.00  --eq_ax_congr_red                       true
% 3.58/1.00  --pure_diseq_elim                       true
% 3.58/1.00  --brand_transform                       false
% 3.58/1.00  --non_eq_to_eq                          false
% 3.58/1.00  --prep_def_merge                        true
% 3.58/1.00  --prep_def_merge_prop_impl              false
% 3.58/1.00  --prep_def_merge_mbd                    true
% 3.58/1.00  --prep_def_merge_tr_red                 false
% 3.58/1.00  --prep_def_merge_tr_cl                  false
% 3.58/1.00  --smt_preprocessing                     true
% 3.58/1.00  --smt_ac_axioms                         fast
% 3.58/1.00  --preprocessed_out                      false
% 3.58/1.00  --preprocessed_stats                    false
% 3.58/1.00  
% 3.58/1.00  ------ Abstraction refinement Options
% 3.58/1.00  
% 3.58/1.00  --abstr_ref                             []
% 3.58/1.00  --abstr_ref_prep                        false
% 3.58/1.00  --abstr_ref_until_sat                   false
% 3.58/1.00  --abstr_ref_sig_restrict                funpre
% 3.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/1.00  --abstr_ref_under                       []
% 3.58/1.00  
% 3.58/1.00  ------ SAT Options
% 3.58/1.00  
% 3.58/1.00  --sat_mode                              false
% 3.58/1.00  --sat_fm_restart_options                ""
% 3.58/1.00  --sat_gr_def                            false
% 3.58/1.00  --sat_epr_types                         true
% 3.58/1.00  --sat_non_cyclic_types                  false
% 3.58/1.00  --sat_finite_models                     false
% 3.58/1.00  --sat_fm_lemmas                         false
% 3.58/1.00  --sat_fm_prep                           false
% 3.58/1.00  --sat_fm_uc_incr                        true
% 3.58/1.00  --sat_out_model                         small
% 3.58/1.00  --sat_out_clauses                       false
% 3.58/1.00  
% 3.58/1.00  ------ QBF Options
% 3.58/1.00  
% 3.58/1.00  --qbf_mode                              false
% 3.58/1.00  --qbf_elim_univ                         false
% 3.58/1.00  --qbf_dom_inst                          none
% 3.58/1.00  --qbf_dom_pre_inst                      false
% 3.58/1.00  --qbf_sk_in                             false
% 3.58/1.00  --qbf_pred_elim                         true
% 3.58/1.00  --qbf_split                             512
% 3.58/1.00  
% 3.58/1.00  ------ BMC1 Options
% 3.58/1.00  
% 3.58/1.00  --bmc1_incremental                      false
% 3.58/1.00  --bmc1_axioms                           reachable_all
% 3.58/1.00  --bmc1_min_bound                        0
% 3.58/1.00  --bmc1_max_bound                        -1
% 3.58/1.00  --bmc1_max_bound_default                -1
% 3.58/1.00  --bmc1_symbol_reachability              true
% 3.58/1.00  --bmc1_property_lemmas                  false
% 3.58/1.00  --bmc1_k_induction                      false
% 3.58/1.00  --bmc1_non_equiv_states                 false
% 3.58/1.00  --bmc1_deadlock                         false
% 3.58/1.00  --bmc1_ucm                              false
% 3.58/1.00  --bmc1_add_unsat_core                   none
% 3.58/1.00  --bmc1_unsat_core_children              false
% 3.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/1.00  --bmc1_out_stat                         full
% 3.58/1.00  --bmc1_ground_init                      false
% 3.58/1.00  --bmc1_pre_inst_next_state              false
% 3.58/1.00  --bmc1_pre_inst_state                   false
% 3.58/1.00  --bmc1_pre_inst_reach_state             false
% 3.58/1.00  --bmc1_out_unsat_core                   false
% 3.58/1.00  --bmc1_aig_witness_out                  false
% 3.58/1.00  --bmc1_verbose                          false
% 3.58/1.00  --bmc1_dump_clauses_tptp                false
% 3.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.58/1.00  --bmc1_dump_file                        -
% 3.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.58/1.00  --bmc1_ucm_extend_mode                  1
% 3.58/1.00  --bmc1_ucm_init_mode                    2
% 3.58/1.00  --bmc1_ucm_cone_mode                    none
% 3.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.58/1.00  --bmc1_ucm_relax_model                  4
% 3.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/1.00  --bmc1_ucm_layered_model                none
% 3.58/1.00  --bmc1_ucm_max_lemma_size               10
% 3.58/1.00  
% 3.58/1.00  ------ AIG Options
% 3.58/1.00  
% 3.58/1.00  --aig_mode                              false
% 3.58/1.00  
% 3.58/1.00  ------ Instantiation Options
% 3.58/1.00  
% 3.58/1.00  --instantiation_flag                    true
% 3.58/1.00  --inst_sos_flag                         false
% 3.58/1.00  --inst_sos_phase                        true
% 3.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/1.00  --inst_lit_sel_side                     none
% 3.58/1.00  --inst_solver_per_active                1400
% 3.58/1.00  --inst_solver_calls_frac                1.
% 3.58/1.00  --inst_passive_queue_type               priority_queues
% 3.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/1.00  --inst_passive_queues_freq              [25;2]
% 3.58/1.00  --inst_dismatching                      true
% 3.58/1.00  --inst_eager_unprocessed_to_passive     true
% 3.58/1.00  --inst_prop_sim_given                   true
% 3.58/1.00  --inst_prop_sim_new                     false
% 3.58/1.00  --inst_subs_new                         false
% 3.58/1.00  --inst_eq_res_simp                      false
% 3.58/1.00  --inst_subs_given                       false
% 3.58/1.00  --inst_orphan_elimination               true
% 3.58/1.00  --inst_learning_loop_flag               true
% 3.58/1.00  --inst_learning_start                   3000
% 3.58/1.00  --inst_learning_factor                  2
% 3.58/1.00  --inst_start_prop_sim_after_learn       3
% 3.58/1.00  --inst_sel_renew                        solver
% 3.58/1.00  --inst_lit_activity_flag                true
% 3.58/1.00  --inst_restr_to_given                   false
% 3.58/1.00  --inst_activity_threshold               500
% 3.58/1.00  --inst_out_proof                        true
% 3.58/1.00  
% 3.58/1.00  ------ Resolution Options
% 3.58/1.00  
% 3.58/1.00  --resolution_flag                       false
% 3.58/1.00  --res_lit_sel                           adaptive
% 3.58/1.00  --res_lit_sel_side                      none
% 3.58/1.00  --res_ordering                          kbo
% 3.58/1.00  --res_to_prop_solver                    active
% 3.58/1.00  --res_prop_simpl_new                    false
% 3.58/1.00  --res_prop_simpl_given                  true
% 3.58/1.00  --res_passive_queue_type                priority_queues
% 3.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/1.00  --res_passive_queues_freq               [15;5]
% 3.58/1.00  --res_forward_subs                      full
% 3.58/1.00  --res_backward_subs                     full
% 3.58/1.00  --res_forward_subs_resolution           true
% 3.58/1.00  --res_backward_subs_resolution          true
% 3.58/1.00  --res_orphan_elimination                true
% 3.58/1.00  --res_time_limit                        2.
% 3.58/1.00  --res_out_proof                         true
% 3.58/1.00  
% 3.58/1.00  ------ Superposition Options
% 3.58/1.00  
% 3.58/1.00  --superposition_flag                    true
% 3.58/1.00  --sup_passive_queue_type                priority_queues
% 3.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.58/1.00  --demod_completeness_check              fast
% 3.58/1.00  --demod_use_ground                      true
% 3.58/1.00  --sup_to_prop_solver                    passive
% 3.58/1.00  --sup_prop_simpl_new                    true
% 3.58/1.00  --sup_prop_simpl_given                  true
% 3.58/1.00  --sup_fun_splitting                     false
% 3.58/1.00  --sup_smt_interval                      50000
% 3.58/1.00  
% 3.58/1.00  ------ Superposition Simplification Setup
% 3.58/1.00  
% 3.58/1.00  --sup_indices_passive                   []
% 3.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/1.00  --sup_full_bw                           [BwDemod]
% 3.58/1.00  --sup_immed_triv                        [TrivRules]
% 3.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/1.00  --sup_immed_bw_main                     []
% 3.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/1.00  
% 3.58/1.00  ------ Combination Options
% 3.58/1.00  
% 3.58/1.00  --comb_res_mult                         3
% 3.58/1.00  --comb_sup_mult                         2
% 3.58/1.00  --comb_inst_mult                        10
% 3.58/1.00  
% 3.58/1.00  ------ Debug Options
% 3.58/1.00  
% 3.58/1.00  --dbg_backtrace                         false
% 3.58/1.00  --dbg_dump_prop_clauses                 false
% 3.58/1.00  --dbg_dump_prop_clauses_file            -
% 3.58/1.00  --dbg_out_stat                          false
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  ------ Proving...
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  % SZS status Theorem for theBenchmark.p
% 3.58/1.00  
% 3.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/1.00  
% 3.58/1.00  fof(f13,conjecture,(
% 3.58/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f14,negated_conjecture,(
% 3.58/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.58/1.00    inference(negated_conjecture,[],[f13])).
% 3.58/1.00  
% 3.58/1.00  fof(f30,plain,(
% 3.58/1.00    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.58/1.00    inference(ennf_transformation,[],[f14])).
% 3.58/1.00  
% 3.58/1.00  fof(f31,plain,(
% 3.58/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.58/1.00    inference(flattening,[],[f30])).
% 3.58/1.00  
% 3.58/1.00  fof(f33,plain,(
% 3.58/1.00    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(sK1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 3.58/1.00    introduced(choice_axiom,[])).
% 3.58/1.00  
% 3.58/1.00  fof(f32,plain,(
% 3.58/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.58/1.00    introduced(choice_axiom,[])).
% 3.58/1.00  
% 3.58/1.00  fof(f34,plain,(
% 3.58/1.00    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(sK1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 3.58/1.00  
% 3.58/1.00  fof(f54,plain,(
% 3.58/1.00    v1_relat_1(sK1)),
% 3.58/1.00    inference(cnf_transformation,[],[f34])).
% 3.58/1.00  
% 3.58/1.00  fof(f52,plain,(
% 3.58/1.00    v1_relat_1(sK0)),
% 3.58/1.00    inference(cnf_transformation,[],[f34])).
% 3.58/1.00  
% 3.58/1.00  fof(f53,plain,(
% 3.58/1.00    v1_funct_1(sK0)),
% 3.58/1.00    inference(cnf_transformation,[],[f34])).
% 3.58/1.00  
% 3.58/1.00  fof(f9,axiom,(
% 3.58/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f24,plain,(
% 3.58/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.58/1.00    inference(ennf_transformation,[],[f9])).
% 3.58/1.00  
% 3.58/1.00  fof(f25,plain,(
% 3.58/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.00    inference(flattening,[],[f24])).
% 3.58/1.00  
% 3.58/1.00  fof(f44,plain,(
% 3.58/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/1.00    inference(cnf_transformation,[],[f25])).
% 3.58/1.00  
% 3.58/1.00  fof(f5,axiom,(
% 3.58/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f20,plain,(
% 3.58/1.00    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.58/1.00    inference(ennf_transformation,[],[f5])).
% 3.58/1.00  
% 3.58/1.00  fof(f39,plain,(
% 3.58/1.00    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/1.00    inference(cnf_transformation,[],[f20])).
% 3.58/1.00  
% 3.58/1.00  fof(f12,axiom,(
% 3.58/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f28,plain,(
% 3.58/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.58/1.00    inference(ennf_transformation,[],[f12])).
% 3.58/1.00  
% 3.58/1.00  fof(f29,plain,(
% 3.58/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.00    inference(flattening,[],[f28])).
% 3.58/1.00  
% 3.58/1.00  fof(f51,plain,(
% 3.58/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/1.00    inference(cnf_transformation,[],[f29])).
% 3.58/1.00  
% 3.58/1.00  fof(f56,plain,(
% 3.58/1.00    v2_funct_1(sK0)),
% 3.58/1.00    inference(cnf_transformation,[],[f34])).
% 3.58/1.00  
% 3.58/1.00  fof(f57,plain,(
% 3.58/1.00    k1_relat_1(sK1) = k2_relat_1(sK0)),
% 3.58/1.00    inference(cnf_transformation,[],[f34])).
% 3.58/1.00  
% 3.58/1.00  fof(f58,plain,(
% 3.58/1.00    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 3.58/1.00    inference(cnf_transformation,[],[f34])).
% 3.58/1.00  
% 3.58/1.00  fof(f8,axiom,(
% 3.58/1.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f23,plain,(
% 3.58/1.00    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.58/1.00    inference(ennf_transformation,[],[f8])).
% 3.58/1.00  
% 3.58/1.00  fof(f43,plain,(
% 3.58/1.00    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.58/1.00    inference(cnf_transformation,[],[f23])).
% 3.58/1.00  
% 3.58/1.00  fof(f11,axiom,(
% 3.58/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f26,plain,(
% 3.58/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.58/1.00    inference(ennf_transformation,[],[f11])).
% 3.58/1.00  
% 3.58/1.00  fof(f27,plain,(
% 3.58/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.58/1.00    inference(flattening,[],[f26])).
% 3.58/1.00  
% 3.58/1.00  fof(f49,plain,(
% 3.58/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/1.00    inference(cnf_transformation,[],[f27])).
% 3.58/1.00  
% 3.58/1.00  fof(f10,axiom,(
% 3.58/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f46,plain,(
% 3.58/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.58/1.00    inference(cnf_transformation,[],[f10])).
% 3.58/1.00  
% 3.58/1.00  fof(f6,axiom,(
% 3.58/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f41,plain,(
% 3.58/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.58/1.00    inference(cnf_transformation,[],[f6])).
% 3.58/1.00  
% 3.58/1.00  fof(f4,axiom,(
% 3.58/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f19,plain,(
% 3.58/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.58/1.00    inference(ennf_transformation,[],[f4])).
% 3.58/1.00  
% 3.58/1.00  fof(f38,plain,(
% 3.58/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.58/1.00    inference(cnf_transformation,[],[f19])).
% 3.58/1.00  
% 3.58/1.00  fof(f40,plain,(
% 3.58/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.58/1.00    inference(cnf_transformation,[],[f6])).
% 3.58/1.00  
% 3.58/1.00  fof(f7,axiom,(
% 3.58/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/1.00  
% 3.58/1.00  fof(f21,plain,(
% 3.58/1.00    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.58/1.00    inference(ennf_transformation,[],[f7])).
% 3.58/1.00  
% 3.58/1.00  fof(f22,plain,(
% 3.58/1.00    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.58/1.00    inference(flattening,[],[f21])).
% 3.58/1.00  
% 3.58/1.00  fof(f42,plain,(
% 3.58/1.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.58/1.00    inference(cnf_transformation,[],[f22])).
% 3.58/1.00  
% 3.58/1.00  fof(f59,plain,(
% 3.58/1.00    k2_funct_1(sK0) != sK1),
% 3.58/1.00    inference(cnf_transformation,[],[f34])).
% 3.58/1.00  
% 3.58/1.00  cnf(c_22,negated_conjecture,
% 3.58/1.00      ( v1_relat_1(sK1) ),
% 3.58/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_710,plain,
% 3.58/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_24,negated_conjecture,
% 3.58/1.00      ( v1_relat_1(sK0) ),
% 3.58/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_708,plain,
% 3.58/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_23,negated_conjecture,
% 3.58/1.00      ( v1_funct_1(sK0) ),
% 3.58/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_709,plain,
% 3.58/1.00      ( v1_funct_1(sK0) = iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_10,plain,
% 3.58/1.00      ( ~ v1_funct_1(X0)
% 3.58/1.00      | ~ v1_relat_1(X0)
% 3.58/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.58/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_713,plain,
% 3.58/1.00      ( v1_funct_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_4,plain,
% 3.58/1.00      ( ~ v1_relat_1(X0)
% 3.58/1.00      | ~ v1_relat_1(X1)
% 3.58/1.00      | ~ v1_relat_1(X2)
% 3.58/1.00      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 3.58/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_717,plain,
% 3.58/1.00      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 3.58/1.00      | v1_relat_1(X1) != iProver_top
% 3.58/1.00      | v1_relat_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_2710,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 3.58/1.00      | v1_funct_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X1) != iProver_top
% 3.58/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_713,c_717]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_12950,plain,
% 3.58/1.00      ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1))
% 3.58/1.00      | v1_relat_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X1) != iProver_top
% 3.58/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_709,c_2710]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_25,plain,
% 3.58/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_19719,plain,
% 3.58/1.00      ( v1_relat_1(X1) != iProver_top
% 3.58/1.00      | v1_relat_1(X0) != iProver_top
% 3.58/1.00      | k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) ),
% 3.58/1.00      inference(global_propositional_subsumption,
% 3.58/1.00                [status(thm)],
% 3.58/1.00                [c_12950,c_25]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_19720,plain,
% 3.58/1.00      ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1))
% 3.58/1.00      | v1_relat_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.58/1.00      inference(renaming,[status(thm)],[c_19719]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_19730,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X0)
% 3.58/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_708,c_19720]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_15,plain,
% 3.58/1.00      ( ~ v2_funct_1(X0)
% 3.58/1.00      | ~ v1_funct_1(X0)
% 3.58/1.00      | ~ v1_relat_1(X0)
% 3.58/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 3.58/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_20,negated_conjecture,
% 3.58/1.00      ( v2_funct_1(sK0) ),
% 3.58/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_338,plain,
% 3.58/1.00      ( ~ v1_funct_1(X0)
% 3.58/1.00      | ~ v1_relat_1(X0)
% 3.58/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 3.58/1.00      | sK0 != X0 ),
% 3.58/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_339,plain,
% 3.58/1.00      ( ~ v1_funct_1(sK0)
% 3.58/1.00      | ~ v1_relat_1(sK0)
% 3.58/1.00      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 3.58/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_34,plain,
% 3.58/1.00      ( ~ v2_funct_1(sK0)
% 3.58/1.00      | ~ v1_funct_1(sK0)
% 3.58/1.00      | ~ v1_relat_1(sK0)
% 3.58/1.00      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 3.58/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_341,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 3.58/1.00      inference(global_propositional_subsumption,
% 3.58/1.00                [status(thm)],
% 3.58/1.00                [c_339,c_24,c_23,c_20,c_34]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_19,negated_conjecture,
% 3.58/1.00      ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
% 3.58/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_747,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
% 3.58/1.00      inference(light_normalisation,[status(thm)],[c_341,c_19]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_19752,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
% 3.58/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.00      inference(light_normalisation,[status(thm)],[c_19730,c_747]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_20171,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_710,c_19752]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_18,negated_conjecture,
% 3.58/1.00      ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 3.58/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_8,plain,
% 3.58/1.00      ( ~ v1_relat_1(X0)
% 3.58/1.00      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.58/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_715,plain,
% 3.58/1.00      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.58/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_1641,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 3.58/1.00      | v1_funct_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_713,c_715]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_5016,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
% 3.58/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_709,c_1641]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_13,plain,
% 3.58/1.00      ( ~ v2_funct_1(X0)
% 3.58/1.00      | ~ v1_funct_1(X0)
% 3.58/1.00      | ~ v1_relat_1(X0)
% 3.58/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.58/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_354,plain,
% 3.58/1.00      ( ~ v1_funct_1(X0)
% 3.58/1.00      | ~ v1_relat_1(X0)
% 3.58/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.58/1.00      | sK0 != X0 ),
% 3.58/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_355,plain,
% 3.58/1.00      ( ~ v1_funct_1(sK0)
% 3.58/1.00      | ~ v1_relat_1(sK0)
% 3.58/1.00      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.58/1.00      inference(unflattening,[status(thm)],[c_354]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_40,plain,
% 3.58/1.00      ( ~ v2_funct_1(sK0)
% 3.58/1.00      | ~ v1_funct_1(sK0)
% 3.58/1.00      | ~ v1_relat_1(sK0)
% 3.58/1.00      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.58/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_357,plain,
% 3.58/1.00      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.58/1.00      inference(global_propositional_subsumption,
% 3.58/1.00                [status(thm)],
% 3.58/1.00                [c_355,c_24,c_23,c_20,c_40]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_5019,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
% 3.58/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.58/1.00      inference(light_normalisation,[status(thm)],[c_5016,c_357]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_5245,plain,
% 3.58/1.00      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
% 3.58/1.00      inference(global_propositional_subsumption,
% 3.58/1.00                [status(thm)],
% 3.58/1.00                [c_5019,c_25]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_12,plain,
% 3.58/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.58/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_712,plain,
% 3.58/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_1445,plain,
% 3.58/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) = k6_relat_1(X0) ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_712,c_715]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_5,plain,
% 3.58/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.58/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_1454,plain,
% 3.58/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.58/1.00      inference(light_normalisation,[status(thm)],[c_1445,c_5]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_3,plain,
% 3.58/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.58/1.00      | ~ v1_relat_1(X1)
% 3.58/1.00      | ~ v1_relat_1(X0) ),
% 3.58/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_718,plain,
% 3.58/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.58/1.00      | v1_relat_1(X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_2422,plain,
% 3.58/1.00      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0))) = iProver_top
% 3.58/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_1454,c_718]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_6,plain,
% 3.58/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.58/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_2448,plain,
% 3.58/1.00      ( r1_tarski(X0,X0) = iProver_top
% 3.58/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.58/1.00      inference(light_normalisation,[status(thm)],[c_2422,c_6]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_42,plain,
% 3.58/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_2873,plain,
% 3.58/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.58/1.00      inference(global_propositional_subsumption,
% 3.58/1.00                [status(thm)],
% 3.58/1.00                [c_2448,c_42]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_7,plain,
% 3.58/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.58/1.00      | ~ v1_relat_1(X0)
% 3.58/1.00      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 3.58/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_716,plain,
% 3.58/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 3.58/1.00      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.58/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.58/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_2880,plain,
% 3.58/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 3.58/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_2873,c_716]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_6293,plain,
% 3.58/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
% 3.58/1.00      inference(superposition,[status(thm)],[c_710,c_2880]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_20189,plain,
% 3.58/1.00      ( k2_funct_1(sK0) = sK1 ),
% 3.58/1.00      inference(light_normalisation,
% 3.58/1.00                [status(thm)],
% 3.58/1.00                [c_20171,c_18,c_5245,c_6293]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(c_17,negated_conjecture,
% 3.58/1.00      ( k2_funct_1(sK0) != sK1 ),
% 3.58/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.58/1.00  
% 3.58/1.00  cnf(contradiction,plain,
% 3.58/1.00      ( $false ),
% 3.58/1.00      inference(minisat,[status(thm)],[c_20189,c_17]) ).
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/1.00  
% 3.58/1.00  ------                               Statistics
% 3.58/1.00  
% 3.58/1.00  ------ General
% 3.58/1.00  
% 3.58/1.00  abstr_ref_over_cycles:                  0
% 3.58/1.00  abstr_ref_under_cycles:                 0
% 3.58/1.00  gc_basic_clause_elim:                   0
% 3.58/1.00  forced_gc_time:                         0
% 3.58/1.00  parsing_time:                           0.008
% 3.58/1.00  unif_index_cands_time:                  0.
% 3.58/1.00  unif_index_add_time:                    0.
% 3.58/1.00  orderings_time:                         0.
% 3.58/1.00  out_proof_time:                         0.008
% 3.58/1.00  total_time:                             0.5
% 3.58/1.00  num_of_symbols:                         43
% 3.58/1.00  num_of_terms:                           15402
% 3.58/1.00  
% 3.58/1.00  ------ Preprocessing
% 3.58/1.00  
% 3.58/1.00  num_of_splits:                          0
% 3.58/1.00  num_of_split_atoms:                     0
% 3.58/1.00  num_of_reused_defs:                     0
% 3.58/1.00  num_eq_ax_congr_red:                    2
% 3.58/1.00  num_of_sem_filtered_clauses:            1
% 3.58/1.00  num_of_subtypes:                        0
% 3.58/1.00  monotx_restored_types:                  0
% 3.58/1.00  sat_num_of_epr_types:                   0
% 3.58/1.00  sat_num_of_non_cyclic_types:            0
% 3.58/1.00  sat_guarded_non_collapsed_types:        0
% 3.58/1.00  num_pure_diseq_elim:                    0
% 3.58/1.00  simp_replaced_by:                       0
% 3.58/1.00  res_preprocessed:                       102
% 3.58/1.00  prep_upred:                             0
% 3.58/1.00  prep_unflattend:                        9
% 3.58/1.00  smt_new_axioms:                         0
% 3.58/1.00  pred_elim_cands:                        4
% 3.58/1.00  pred_elim:                              1
% 3.58/1.00  pred_elim_cl:                           -2
% 3.58/1.00  pred_elim_cycles:                       3
% 3.58/1.00  merged_defs:                            0
% 3.58/1.00  merged_defs_ncl:                        0
% 3.58/1.00  bin_hyper_res:                          0
% 3.58/1.00  prep_cycles:                            3
% 3.58/1.00  pred_elim_time:                         0.002
% 3.58/1.00  splitting_time:                         0.
% 3.58/1.00  sem_filter_time:                        0.
% 3.58/1.00  monotx_time:                            0.001
% 3.58/1.00  subtype_inf_time:                       0.
% 3.58/1.00  
% 3.58/1.00  ------ Problem properties
% 3.58/1.00  
% 3.58/1.00  clauses:                                27
% 3.58/1.00  conjectures:                            7
% 3.58/1.00  epr:                                    4
% 3.58/1.00  horn:                                   27
% 3.58/1.00  ground:                                 11
% 3.58/1.00  unary:                                  14
% 3.58/1.00  binary:                                 6
% 3.58/1.00  lits:                                   48
% 3.58/1.00  lits_eq:                                18
% 3.58/1.00  fd_pure:                                0
% 3.58/1.00  fd_pseudo:                              0
% 3.58/1.00  fd_cond:                                0
% 3.58/1.00  fd_pseudo_cond:                         0
% 3.58/1.00  ac_symbols:                             0
% 3.58/1.00  
% 3.58/1.00  ------ Propositional Solver
% 3.58/1.00  
% 3.58/1.00  prop_solver_calls:                      25
% 3.58/1.00  prop_fast_solver_calls:                 834
% 3.58/1.00  smt_solver_calls:                       0
% 3.58/1.00  smt_fast_solver_calls:                  0
% 3.58/1.00  prop_num_of_clauses:                    5987
% 3.58/1.00  prop_preprocess_simplified:             10957
% 3.58/1.00  prop_fo_subsumed:                       43
% 3.58/1.00  prop_solver_time:                       0.
% 3.58/1.00  smt_solver_time:                        0.
% 3.58/1.00  smt_fast_solver_time:                   0.
% 3.58/1.00  prop_fast_solver_time:                  0.
% 3.58/1.00  prop_unsat_core_time:                   0.
% 3.58/1.00  
% 3.58/1.00  ------ QBF
% 3.58/1.00  
% 3.58/1.00  qbf_q_res:                              0
% 3.58/1.00  qbf_num_tautologies:                    0
% 3.58/1.00  qbf_prep_cycles:                        0
% 3.58/1.00  
% 3.58/1.00  ------ BMC1
% 3.58/1.00  
% 3.58/1.00  bmc1_current_bound:                     -1
% 3.58/1.00  bmc1_last_solved_bound:                 -1
% 3.58/1.00  bmc1_unsat_core_size:                   -1
% 3.58/1.00  bmc1_unsat_core_parents_size:           -1
% 3.58/1.00  bmc1_merge_next_fun:                    0
% 3.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.58/1.00  
% 3.58/1.00  ------ Instantiation
% 3.58/1.00  
% 3.58/1.00  inst_num_of_clauses:                    2426
% 3.58/1.00  inst_num_in_passive:                    426
% 3.58/1.00  inst_num_in_active:                     904
% 3.58/1.00  inst_num_in_unprocessed:                1096
% 3.58/1.00  inst_num_of_loops:                      940
% 3.58/1.00  inst_num_of_learning_restarts:          0
% 3.58/1.00  inst_num_moves_active_passive:          34
% 3.58/1.00  inst_lit_activity:                      0
% 3.58/1.00  inst_lit_activity_moves:                0
% 3.58/1.00  inst_num_tautologies:                   0
% 3.58/1.00  inst_num_prop_implied:                  0
% 3.58/1.00  inst_num_existing_simplified:           0
% 3.58/1.00  inst_num_eq_res_simplified:             0
% 3.58/1.00  inst_num_child_elim:                    0
% 3.58/1.00  inst_num_of_dismatching_blockings:      3892
% 3.58/1.00  inst_num_of_non_proper_insts:           4004
% 3.58/1.00  inst_num_of_duplicates:                 0
% 3.58/1.00  inst_inst_num_from_inst_to_res:         0
% 3.58/1.00  inst_dismatching_checking_time:         0.
% 3.58/1.00  
% 3.58/1.00  ------ Resolution
% 3.58/1.00  
% 3.58/1.00  res_num_of_clauses:                     0
% 3.58/1.00  res_num_in_passive:                     0
% 3.58/1.00  res_num_in_active:                      0
% 3.58/1.00  res_num_of_loops:                       105
% 3.58/1.00  res_forward_subset_subsumed:            490
% 3.58/1.00  res_backward_subset_subsumed:           4
% 3.58/1.00  res_forward_subsumed:                   0
% 3.58/1.00  res_backward_subsumed:                  0
% 3.58/1.00  res_forward_subsumption_resolution:     0
% 3.58/1.00  res_backward_subsumption_resolution:    0
% 3.58/1.00  res_clause_to_clause_subsumption:       1911
% 3.58/1.00  res_orphan_elimination:                 0
% 3.58/1.00  res_tautology_del:                      298
% 3.58/1.00  res_num_eq_res_simplified:              0
% 3.58/1.00  res_num_sel_changes:                    0
% 3.58/1.00  res_moves_from_active_to_pass:          0
% 3.58/1.00  
% 3.58/1.00  ------ Superposition
% 3.58/1.00  
% 3.58/1.00  sup_time_total:                         0.
% 3.58/1.00  sup_time_generating:                    0.
% 3.58/1.00  sup_time_sim_full:                      0.
% 3.58/1.00  sup_time_sim_immed:                     0.
% 3.58/1.00  
% 3.58/1.00  sup_num_of_clauses:                     555
% 3.58/1.00  sup_num_in_active:                      184
% 3.58/1.00  sup_num_in_passive:                     371
% 3.58/1.00  sup_num_of_loops:                       186
% 3.58/1.00  sup_fw_superposition:                   386
% 3.58/1.00  sup_bw_superposition:                   274
% 3.58/1.00  sup_immediate_simplified:               141
% 3.58/1.00  sup_given_eliminated:                   1
% 3.58/1.00  comparisons_done:                       0
% 3.58/1.00  comparisons_avoided:                    0
% 3.58/1.00  
% 3.58/1.00  ------ Simplifications
% 3.58/1.00  
% 3.58/1.00  
% 3.58/1.00  sim_fw_subset_subsumed:                 17
% 3.58/1.00  sim_bw_subset_subsumed:                 5
% 3.58/1.00  sim_fw_subsumed:                        29
% 3.58/1.00  sim_bw_subsumed:                        0
% 3.58/1.00  sim_fw_subsumption_res:                 2
% 3.58/1.00  sim_bw_subsumption_res:                 0
% 3.58/1.00  sim_tautology_del:                      26
% 3.58/1.00  sim_eq_tautology_del:                   19
% 3.58/1.00  sim_eq_res_simp:                        0
% 3.58/1.00  sim_fw_demodulated:                     35
% 3.58/1.00  sim_bw_demodulated:                     8
% 3.58/1.00  sim_light_normalised:                   97
% 3.58/1.00  sim_joinable_taut:                      0
% 3.58/1.00  sim_joinable_simp:                      0
% 3.58/1.00  sim_ac_normalised:                      0
% 3.58/1.00  sim_smt_subsumption:                    0
% 3.58/1.00  
%------------------------------------------------------------------------------
