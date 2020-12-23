%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:47 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 701 expanded)
%              Number of clauses        :   65 ( 182 expanded)
%              Number of leaves         :    9 ( 183 expanded)
%              Depth                    :   18
%              Number of atoms          :  287 (4397 expanded)
%              Number of equality atoms :  118 (1625 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(sK1)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k2_relat_1(sK0) = k1_relat_1(X1)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_274,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_433,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_273,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_434,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_177,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_178,plain,
    ( ~ v1_funct_1(sK0)
    | v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_29,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_180,plain,
    ( v1_relat_1(k4_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_16,c_15,c_12,c_29])).

cnf(c_270,plain,
    ( v1_relat_1(k4_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_435,plain,
    ( v1_relat_1(k4_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_279,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X2_39)
    | k5_relat_1(k5_relat_1(X0_39,X2_39),X1_39) = k5_relat_1(X0_39,k5_relat_1(X2_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_431,plain,
    ( k5_relat_1(k5_relat_1(X0_39,X1_39),X2_39) = k5_relat_1(X0_39,k5_relat_1(X1_39,X2_39))
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X2_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_964,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0_39,X1_39)) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0_39),X1_39)
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_431])).

cnf(c_1531,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),X0_39) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0_39))
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_434,c_964])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_169,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_170,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_26,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_172,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_170,c_16,c_15,c_12,c_26])).

cnf(c_271,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_172])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_199,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_200,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_35,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_202,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_16,c_15,c_12,c_35])).

cnf(c_269,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_456,plain,
    ( k5_relat_1(k4_relat_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_271,c_269])).

cnf(c_1539,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0_39)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1531,c_456])).

cnf(c_2306,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    inference(superposition,[status(thm)],[c_433,c_1539])).

cnf(c_10,negated_conjecture,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_276,negated_conjecture,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_278,plain,
    ( ~ v1_relat_1(X0_39)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_432,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_662,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_433,c_432])).

cnf(c_11,negated_conjecture,
    ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_275,negated_conjecture,
    ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_670,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_662,c_275])).

cnf(c_2315,plain,
    ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2306,c_276,c_670])).

cnf(c_2308,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,k4_relat_1(sK0))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_435,c_1539])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_161,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_162,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_23,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_164,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_162,c_16,c_15,c_12,c_23])).

cnf(c_272,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_164])).

cnf(c_453,plain,
    ( k5_relat_1(sK0,k4_relat_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_272,c_269])).

cnf(c_664,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_435,c_432])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_280,plain,
    ( ~ v1_relat_1(X0_39)
    | k1_relat_1(k4_relat_1(X0_39)) = k2_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_430,plain,
    ( k1_relat_1(k4_relat_1(X0_39)) = k2_relat_1(X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_651,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_434,c_430])).

cnf(c_955,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_664,c_651])).

cnf(c_2310,plain,
    ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k4_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2308,c_453,c_955])).

cnf(c_2316,plain,
    ( k4_relat_1(sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_2315,c_2310])).

cnf(c_9,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_277,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_447,plain,
    ( k4_relat_1(sK0) != sK1 ),
    inference(demodulation,[status(thm)],[c_269,c_277])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2316,c_447])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n007.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 10:30:21 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 2.38/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.03  
% 2.38/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.38/1.03  
% 2.38/1.03  ------  iProver source info
% 2.38/1.03  
% 2.38/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.38/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.38/1.03  git: non_committed_changes: false
% 2.38/1.03  git: last_make_outside_of_git: false
% 2.38/1.03  
% 2.38/1.03  ------ 
% 2.38/1.03  
% 2.38/1.03  ------ Input Options
% 2.38/1.03  
% 2.38/1.03  --out_options                           all
% 2.38/1.03  --tptp_safe_out                         true
% 2.38/1.03  --problem_path                          ""
% 2.38/1.03  --include_path                          ""
% 2.38/1.03  --clausifier                            res/vclausify_rel
% 2.38/1.03  --clausifier_options                    --mode clausify
% 2.38/1.03  --stdin                                 false
% 2.38/1.03  --stats_out                             all
% 2.38/1.03  
% 2.38/1.03  ------ General Options
% 2.38/1.03  
% 2.38/1.03  --fof                                   false
% 2.38/1.03  --time_out_real                         305.
% 2.38/1.03  --time_out_virtual                      -1.
% 2.38/1.03  --symbol_type_check                     false
% 2.38/1.03  --clausify_out                          false
% 2.38/1.03  --sig_cnt_out                           false
% 2.38/1.03  --trig_cnt_out                          false
% 2.38/1.03  --trig_cnt_out_tolerance                1.
% 2.38/1.03  --trig_cnt_out_sk_spl                   false
% 2.38/1.03  --abstr_cl_out                          false
% 2.38/1.03  
% 2.38/1.03  ------ Global Options
% 2.38/1.03  
% 2.38/1.03  --schedule                              default
% 2.38/1.03  --add_important_lit                     false
% 2.38/1.03  --prop_solver_per_cl                    1000
% 2.38/1.03  --min_unsat_core                        false
% 2.38/1.03  --soft_assumptions                      false
% 2.38/1.03  --soft_lemma_size                       3
% 2.38/1.03  --prop_impl_unit_size                   0
% 2.38/1.03  --prop_impl_unit                        []
% 2.38/1.03  --share_sel_clauses                     true
% 2.38/1.03  --reset_solvers                         false
% 2.38/1.03  --bc_imp_inh                            [conj_cone]
% 2.38/1.03  --conj_cone_tolerance                   3.
% 2.38/1.03  --extra_neg_conj                        none
% 2.38/1.03  --large_theory_mode                     true
% 2.38/1.03  --prolific_symb_bound                   200
% 2.38/1.03  --lt_threshold                          2000
% 2.38/1.03  --clause_weak_htbl                      true
% 2.38/1.03  --gc_record_bc_elim                     false
% 2.38/1.03  
% 2.38/1.03  ------ Preprocessing Options
% 2.38/1.03  
% 2.38/1.03  --preprocessing_flag                    true
% 2.38/1.03  --time_out_prep_mult                    0.1
% 2.38/1.03  --splitting_mode                        input
% 2.38/1.03  --splitting_grd                         true
% 2.38/1.03  --splitting_cvd                         false
% 2.38/1.03  --splitting_cvd_svl                     false
% 2.38/1.03  --splitting_nvd                         32
% 2.38/1.03  --sub_typing                            true
% 2.38/1.03  --prep_gs_sim                           true
% 2.38/1.03  --prep_unflatten                        true
% 2.38/1.03  --prep_res_sim                          true
% 2.38/1.03  --prep_upred                            true
% 2.38/1.03  --prep_sem_filter                       exhaustive
% 2.38/1.03  --prep_sem_filter_out                   false
% 2.38/1.03  --pred_elim                             true
% 2.38/1.03  --res_sim_input                         true
% 2.38/1.03  --eq_ax_congr_red                       true
% 2.38/1.03  --pure_diseq_elim                       true
% 2.38/1.03  --brand_transform                       false
% 2.38/1.03  --non_eq_to_eq                          false
% 2.38/1.03  --prep_def_merge                        true
% 2.38/1.03  --prep_def_merge_prop_impl              false
% 2.38/1.03  --prep_def_merge_mbd                    true
% 2.38/1.03  --prep_def_merge_tr_red                 false
% 2.38/1.03  --prep_def_merge_tr_cl                  false
% 2.38/1.03  --smt_preprocessing                     true
% 2.38/1.03  --smt_ac_axioms                         fast
% 2.38/1.03  --preprocessed_out                      false
% 2.38/1.03  --preprocessed_stats                    false
% 2.38/1.03  
% 2.38/1.03  ------ Abstraction refinement Options
% 2.38/1.03  
% 2.38/1.03  --abstr_ref                             []
% 2.38/1.03  --abstr_ref_prep                        false
% 2.38/1.03  --abstr_ref_until_sat                   false
% 2.38/1.03  --abstr_ref_sig_restrict                funpre
% 2.38/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.03  --abstr_ref_under                       []
% 2.38/1.03  
% 2.38/1.03  ------ SAT Options
% 2.38/1.03  
% 2.38/1.03  --sat_mode                              false
% 2.38/1.03  --sat_fm_restart_options                ""
% 2.38/1.03  --sat_gr_def                            false
% 2.38/1.03  --sat_epr_types                         true
% 2.38/1.03  --sat_non_cyclic_types                  false
% 2.38/1.03  --sat_finite_models                     false
% 2.38/1.03  --sat_fm_lemmas                         false
% 2.38/1.03  --sat_fm_prep                           false
% 2.38/1.03  --sat_fm_uc_incr                        true
% 2.38/1.03  --sat_out_model                         small
% 2.38/1.03  --sat_out_clauses                       false
% 2.38/1.03  
% 2.38/1.03  ------ QBF Options
% 2.38/1.03  
% 2.38/1.03  --qbf_mode                              false
% 2.38/1.03  --qbf_elim_univ                         false
% 2.38/1.03  --qbf_dom_inst                          none
% 2.38/1.03  --qbf_dom_pre_inst                      false
% 2.38/1.03  --qbf_sk_in                             false
% 2.38/1.03  --qbf_pred_elim                         true
% 2.38/1.03  --qbf_split                             512
% 2.38/1.03  
% 2.38/1.03  ------ BMC1 Options
% 2.38/1.03  
% 2.38/1.03  --bmc1_incremental                      false
% 2.38/1.03  --bmc1_axioms                           reachable_all
% 2.38/1.03  --bmc1_min_bound                        0
% 2.38/1.03  --bmc1_max_bound                        -1
% 2.38/1.03  --bmc1_max_bound_default                -1
% 2.38/1.03  --bmc1_symbol_reachability              true
% 2.38/1.03  --bmc1_property_lemmas                  false
% 2.38/1.03  --bmc1_k_induction                      false
% 2.38/1.03  --bmc1_non_equiv_states                 false
% 2.38/1.03  --bmc1_deadlock                         false
% 2.38/1.03  --bmc1_ucm                              false
% 2.38/1.03  --bmc1_add_unsat_core                   none
% 2.38/1.03  --bmc1_unsat_core_children              false
% 2.38/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.03  --bmc1_out_stat                         full
% 2.38/1.03  --bmc1_ground_init                      false
% 2.38/1.03  --bmc1_pre_inst_next_state              false
% 2.38/1.03  --bmc1_pre_inst_state                   false
% 2.38/1.03  --bmc1_pre_inst_reach_state             false
% 2.38/1.03  --bmc1_out_unsat_core                   false
% 2.38/1.03  --bmc1_aig_witness_out                  false
% 2.38/1.03  --bmc1_verbose                          false
% 2.38/1.03  --bmc1_dump_clauses_tptp                false
% 2.38/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.03  --bmc1_dump_file                        -
% 2.38/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.03  --bmc1_ucm_extend_mode                  1
% 2.38/1.03  --bmc1_ucm_init_mode                    2
% 2.38/1.03  --bmc1_ucm_cone_mode                    none
% 2.38/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.03  --bmc1_ucm_relax_model                  4
% 2.38/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.03  --bmc1_ucm_layered_model                none
% 2.38/1.03  --bmc1_ucm_max_lemma_size               10
% 2.38/1.03  
% 2.38/1.03  ------ AIG Options
% 2.38/1.03  
% 2.38/1.03  --aig_mode                              false
% 2.38/1.03  
% 2.38/1.03  ------ Instantiation Options
% 2.38/1.03  
% 2.38/1.03  --instantiation_flag                    true
% 2.38/1.03  --inst_sos_flag                         false
% 2.38/1.03  --inst_sos_phase                        true
% 2.38/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.03  --inst_lit_sel_side                     num_symb
% 2.38/1.03  --inst_solver_per_active                1400
% 2.38/1.03  --inst_solver_calls_frac                1.
% 2.38/1.03  --inst_passive_queue_type               priority_queues
% 2.38/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.03  --inst_passive_queues_freq              [25;2]
% 2.38/1.03  --inst_dismatching                      true
% 2.38/1.03  --inst_eager_unprocessed_to_passive     true
% 2.38/1.03  --inst_prop_sim_given                   true
% 2.38/1.03  --inst_prop_sim_new                     false
% 2.38/1.03  --inst_subs_new                         false
% 2.38/1.03  --inst_eq_res_simp                      false
% 2.38/1.03  --inst_subs_given                       false
% 2.38/1.03  --inst_orphan_elimination               true
% 2.38/1.03  --inst_learning_loop_flag               true
% 2.38/1.03  --inst_learning_start                   3000
% 2.38/1.03  --inst_learning_factor                  2
% 2.38/1.03  --inst_start_prop_sim_after_learn       3
% 2.38/1.03  --inst_sel_renew                        solver
% 2.38/1.03  --inst_lit_activity_flag                true
% 2.38/1.03  --inst_restr_to_given                   false
% 2.38/1.03  --inst_activity_threshold               500
% 2.38/1.03  --inst_out_proof                        true
% 2.38/1.03  
% 2.38/1.03  ------ Resolution Options
% 2.38/1.03  
% 2.38/1.03  --resolution_flag                       true
% 2.38/1.03  --res_lit_sel                           adaptive
% 2.38/1.03  --res_lit_sel_side                      none
% 2.38/1.03  --res_ordering                          kbo
% 2.38/1.03  --res_to_prop_solver                    active
% 2.38/1.03  --res_prop_simpl_new                    false
% 2.38/1.03  --res_prop_simpl_given                  true
% 2.38/1.03  --res_passive_queue_type                priority_queues
% 2.38/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.03  --res_passive_queues_freq               [15;5]
% 2.38/1.03  --res_forward_subs                      full
% 2.38/1.03  --res_backward_subs                     full
% 2.38/1.03  --res_forward_subs_resolution           true
% 2.38/1.03  --res_backward_subs_resolution          true
% 2.38/1.03  --res_orphan_elimination                true
% 2.38/1.03  --res_time_limit                        2.
% 2.38/1.03  --res_out_proof                         true
% 2.38/1.03  
% 2.38/1.03  ------ Superposition Options
% 2.38/1.03  
% 2.38/1.03  --superposition_flag                    true
% 2.38/1.03  --sup_passive_queue_type                priority_queues
% 2.38/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.03  --demod_completeness_check              fast
% 2.38/1.03  --demod_use_ground                      true
% 2.38/1.03  --sup_to_prop_solver                    passive
% 2.38/1.03  --sup_prop_simpl_new                    true
% 2.38/1.03  --sup_prop_simpl_given                  true
% 2.38/1.03  --sup_fun_splitting                     false
% 2.38/1.03  --sup_smt_interval                      50000
% 2.38/1.03  
% 2.38/1.03  ------ Superposition Simplification Setup
% 2.38/1.03  
% 2.38/1.03  --sup_indices_passive                   []
% 2.38/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.03  --sup_full_bw                           [BwDemod]
% 2.38/1.03  --sup_immed_triv                        [TrivRules]
% 2.38/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.03  --sup_immed_bw_main                     []
% 2.38/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.03  
% 2.38/1.03  ------ Combination Options
% 2.38/1.03  
% 2.38/1.03  --comb_res_mult                         3
% 2.38/1.03  --comb_sup_mult                         2
% 2.38/1.03  --comb_inst_mult                        10
% 2.38/1.03  
% 2.38/1.03  ------ Debug Options
% 2.38/1.03  
% 2.38/1.03  --dbg_backtrace                         false
% 2.38/1.03  --dbg_dump_prop_clauses                 false
% 2.38/1.03  --dbg_dump_prop_clauses_file            -
% 2.38/1.03  --dbg_out_stat                          false
% 2.38/1.03  ------ Parsing...
% 2.38/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.38/1.03  
% 2.38/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.38/1.03  
% 2.38/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.38/1.03  
% 2.38/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.38/1.03  ------ Proving...
% 2.38/1.03  ------ Problem Properties 
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  clauses                                 13
% 2.38/1.03  conjectures                             5
% 2.38/1.03  EPR                                     2
% 2.38/1.03  Horn                                    13
% 2.38/1.03  unary                                   9
% 2.38/1.03  binary                                  3
% 2.38/1.03  lits                                    19
% 2.38/1.03  lits eq                                 10
% 2.38/1.03  fd_pure                                 0
% 2.38/1.03  fd_pseudo                               0
% 2.38/1.03  fd_cond                                 0
% 2.38/1.03  fd_pseudo_cond                          0
% 2.38/1.03  AC symbols                              0
% 2.38/1.03  
% 2.38/1.03  ------ Schedule dynamic 5 is on 
% 2.38/1.03  
% 2.38/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  ------ 
% 2.38/1.03  Current options:
% 2.38/1.03  ------ 
% 2.38/1.03  
% 2.38/1.03  ------ Input Options
% 2.38/1.03  
% 2.38/1.03  --out_options                           all
% 2.38/1.03  --tptp_safe_out                         true
% 2.38/1.03  --problem_path                          ""
% 2.38/1.03  --include_path                          ""
% 2.38/1.03  --clausifier                            res/vclausify_rel
% 2.38/1.03  --clausifier_options                    --mode clausify
% 2.38/1.03  --stdin                                 false
% 2.38/1.03  --stats_out                             all
% 2.38/1.03  
% 2.38/1.03  ------ General Options
% 2.38/1.03  
% 2.38/1.03  --fof                                   false
% 2.38/1.03  --time_out_real                         305.
% 2.38/1.03  --time_out_virtual                      -1.
% 2.38/1.03  --symbol_type_check                     false
% 2.38/1.03  --clausify_out                          false
% 2.38/1.03  --sig_cnt_out                           false
% 2.38/1.03  --trig_cnt_out                          false
% 2.38/1.03  --trig_cnt_out_tolerance                1.
% 2.38/1.03  --trig_cnt_out_sk_spl                   false
% 2.38/1.03  --abstr_cl_out                          false
% 2.38/1.03  
% 2.38/1.03  ------ Global Options
% 2.38/1.03  
% 2.38/1.03  --schedule                              default
% 2.38/1.03  --add_important_lit                     false
% 2.38/1.03  --prop_solver_per_cl                    1000
% 2.38/1.03  --min_unsat_core                        false
% 2.38/1.03  --soft_assumptions                      false
% 2.38/1.03  --soft_lemma_size                       3
% 2.38/1.03  --prop_impl_unit_size                   0
% 2.38/1.03  --prop_impl_unit                        []
% 2.38/1.03  --share_sel_clauses                     true
% 2.38/1.03  --reset_solvers                         false
% 2.38/1.03  --bc_imp_inh                            [conj_cone]
% 2.38/1.03  --conj_cone_tolerance                   3.
% 2.38/1.03  --extra_neg_conj                        none
% 2.38/1.03  --large_theory_mode                     true
% 2.38/1.03  --prolific_symb_bound                   200
% 2.38/1.03  --lt_threshold                          2000
% 2.38/1.03  --clause_weak_htbl                      true
% 2.38/1.03  --gc_record_bc_elim                     false
% 2.38/1.03  
% 2.38/1.03  ------ Preprocessing Options
% 2.38/1.03  
% 2.38/1.03  --preprocessing_flag                    true
% 2.38/1.03  --time_out_prep_mult                    0.1
% 2.38/1.03  --splitting_mode                        input
% 2.38/1.03  --splitting_grd                         true
% 2.38/1.03  --splitting_cvd                         false
% 2.38/1.03  --splitting_cvd_svl                     false
% 2.38/1.03  --splitting_nvd                         32
% 2.38/1.03  --sub_typing                            true
% 2.38/1.03  --prep_gs_sim                           true
% 2.38/1.03  --prep_unflatten                        true
% 2.38/1.03  --prep_res_sim                          true
% 2.38/1.03  --prep_upred                            true
% 2.38/1.03  --prep_sem_filter                       exhaustive
% 2.38/1.03  --prep_sem_filter_out                   false
% 2.38/1.03  --pred_elim                             true
% 2.38/1.03  --res_sim_input                         true
% 2.38/1.03  --eq_ax_congr_red                       true
% 2.38/1.03  --pure_diseq_elim                       true
% 2.38/1.03  --brand_transform                       false
% 2.38/1.03  --non_eq_to_eq                          false
% 2.38/1.03  --prep_def_merge                        true
% 2.38/1.03  --prep_def_merge_prop_impl              false
% 2.38/1.03  --prep_def_merge_mbd                    true
% 2.38/1.03  --prep_def_merge_tr_red                 false
% 2.38/1.03  --prep_def_merge_tr_cl                  false
% 2.38/1.03  --smt_preprocessing                     true
% 2.38/1.03  --smt_ac_axioms                         fast
% 2.38/1.03  --preprocessed_out                      false
% 2.38/1.03  --preprocessed_stats                    false
% 2.38/1.03  
% 2.38/1.03  ------ Abstraction refinement Options
% 2.38/1.03  
% 2.38/1.03  --abstr_ref                             []
% 2.38/1.03  --abstr_ref_prep                        false
% 2.38/1.03  --abstr_ref_until_sat                   false
% 2.38/1.03  --abstr_ref_sig_restrict                funpre
% 2.38/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.03  --abstr_ref_under                       []
% 2.38/1.03  
% 2.38/1.03  ------ SAT Options
% 2.38/1.03  
% 2.38/1.03  --sat_mode                              false
% 2.38/1.03  --sat_fm_restart_options                ""
% 2.38/1.03  --sat_gr_def                            false
% 2.38/1.03  --sat_epr_types                         true
% 2.38/1.03  --sat_non_cyclic_types                  false
% 2.38/1.03  --sat_finite_models                     false
% 2.38/1.03  --sat_fm_lemmas                         false
% 2.38/1.03  --sat_fm_prep                           false
% 2.38/1.03  --sat_fm_uc_incr                        true
% 2.38/1.03  --sat_out_model                         small
% 2.38/1.03  --sat_out_clauses                       false
% 2.38/1.03  
% 2.38/1.03  ------ QBF Options
% 2.38/1.03  
% 2.38/1.03  --qbf_mode                              false
% 2.38/1.03  --qbf_elim_univ                         false
% 2.38/1.03  --qbf_dom_inst                          none
% 2.38/1.03  --qbf_dom_pre_inst                      false
% 2.38/1.03  --qbf_sk_in                             false
% 2.38/1.03  --qbf_pred_elim                         true
% 2.38/1.03  --qbf_split                             512
% 2.38/1.03  
% 2.38/1.03  ------ BMC1 Options
% 2.38/1.03  
% 2.38/1.03  --bmc1_incremental                      false
% 2.38/1.03  --bmc1_axioms                           reachable_all
% 2.38/1.03  --bmc1_min_bound                        0
% 2.38/1.03  --bmc1_max_bound                        -1
% 2.38/1.03  --bmc1_max_bound_default                -1
% 2.38/1.03  --bmc1_symbol_reachability              true
% 2.38/1.03  --bmc1_property_lemmas                  false
% 2.38/1.03  --bmc1_k_induction                      false
% 2.38/1.03  --bmc1_non_equiv_states                 false
% 2.38/1.03  --bmc1_deadlock                         false
% 2.38/1.03  --bmc1_ucm                              false
% 2.38/1.03  --bmc1_add_unsat_core                   none
% 2.38/1.03  --bmc1_unsat_core_children              false
% 2.38/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.03  --bmc1_out_stat                         full
% 2.38/1.03  --bmc1_ground_init                      false
% 2.38/1.03  --bmc1_pre_inst_next_state              false
% 2.38/1.03  --bmc1_pre_inst_state                   false
% 2.38/1.03  --bmc1_pre_inst_reach_state             false
% 2.38/1.03  --bmc1_out_unsat_core                   false
% 2.38/1.03  --bmc1_aig_witness_out                  false
% 2.38/1.03  --bmc1_verbose                          false
% 2.38/1.03  --bmc1_dump_clauses_tptp                false
% 2.38/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.03  --bmc1_dump_file                        -
% 2.38/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.03  --bmc1_ucm_extend_mode                  1
% 2.38/1.03  --bmc1_ucm_init_mode                    2
% 2.38/1.03  --bmc1_ucm_cone_mode                    none
% 2.38/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.03  --bmc1_ucm_relax_model                  4
% 2.38/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.03  --bmc1_ucm_layered_model                none
% 2.38/1.03  --bmc1_ucm_max_lemma_size               10
% 2.38/1.03  
% 2.38/1.03  ------ AIG Options
% 2.38/1.03  
% 2.38/1.03  --aig_mode                              false
% 2.38/1.03  
% 2.38/1.03  ------ Instantiation Options
% 2.38/1.03  
% 2.38/1.03  --instantiation_flag                    true
% 2.38/1.03  --inst_sos_flag                         false
% 2.38/1.03  --inst_sos_phase                        true
% 2.38/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.03  --inst_lit_sel_side                     none
% 2.38/1.03  --inst_solver_per_active                1400
% 2.38/1.03  --inst_solver_calls_frac                1.
% 2.38/1.03  --inst_passive_queue_type               priority_queues
% 2.38/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.03  --inst_passive_queues_freq              [25;2]
% 2.38/1.03  --inst_dismatching                      true
% 2.38/1.03  --inst_eager_unprocessed_to_passive     true
% 2.38/1.03  --inst_prop_sim_given                   true
% 2.38/1.03  --inst_prop_sim_new                     false
% 2.38/1.03  --inst_subs_new                         false
% 2.38/1.03  --inst_eq_res_simp                      false
% 2.38/1.03  --inst_subs_given                       false
% 2.38/1.03  --inst_orphan_elimination               true
% 2.38/1.03  --inst_learning_loop_flag               true
% 2.38/1.03  --inst_learning_start                   3000
% 2.38/1.03  --inst_learning_factor                  2
% 2.38/1.03  --inst_start_prop_sim_after_learn       3
% 2.38/1.03  --inst_sel_renew                        solver
% 2.38/1.03  --inst_lit_activity_flag                true
% 2.38/1.03  --inst_restr_to_given                   false
% 2.38/1.03  --inst_activity_threshold               500
% 2.38/1.03  --inst_out_proof                        true
% 2.38/1.03  
% 2.38/1.03  ------ Resolution Options
% 2.38/1.03  
% 2.38/1.03  --resolution_flag                       false
% 2.38/1.03  --res_lit_sel                           adaptive
% 2.38/1.03  --res_lit_sel_side                      none
% 2.38/1.03  --res_ordering                          kbo
% 2.38/1.03  --res_to_prop_solver                    active
% 2.38/1.03  --res_prop_simpl_new                    false
% 2.38/1.03  --res_prop_simpl_given                  true
% 2.38/1.03  --res_passive_queue_type                priority_queues
% 2.38/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.03  --res_passive_queues_freq               [15;5]
% 2.38/1.03  --res_forward_subs                      full
% 2.38/1.03  --res_backward_subs                     full
% 2.38/1.03  --res_forward_subs_resolution           true
% 2.38/1.03  --res_backward_subs_resolution          true
% 2.38/1.03  --res_orphan_elimination                true
% 2.38/1.03  --res_time_limit                        2.
% 2.38/1.03  --res_out_proof                         true
% 2.38/1.03  
% 2.38/1.03  ------ Superposition Options
% 2.38/1.03  
% 2.38/1.03  --superposition_flag                    true
% 2.38/1.03  --sup_passive_queue_type                priority_queues
% 2.38/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.03  --demod_completeness_check              fast
% 2.38/1.03  --demod_use_ground                      true
% 2.38/1.03  --sup_to_prop_solver                    passive
% 2.38/1.03  --sup_prop_simpl_new                    true
% 2.38/1.03  --sup_prop_simpl_given                  true
% 2.38/1.03  --sup_fun_splitting                     false
% 2.38/1.03  --sup_smt_interval                      50000
% 2.38/1.03  
% 2.38/1.03  ------ Superposition Simplification Setup
% 2.38/1.03  
% 2.38/1.03  --sup_indices_passive                   []
% 2.38/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.03  --sup_full_bw                           [BwDemod]
% 2.38/1.03  --sup_immed_triv                        [TrivRules]
% 2.38/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.03  --sup_immed_bw_main                     []
% 2.38/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.03  
% 2.38/1.03  ------ Combination Options
% 2.38/1.03  
% 2.38/1.03  --comb_res_mult                         3
% 2.38/1.03  --comb_sup_mult                         2
% 2.38/1.03  --comb_inst_mult                        10
% 2.38/1.03  
% 2.38/1.03  ------ Debug Options
% 2.38/1.03  
% 2.38/1.03  --dbg_backtrace                         false
% 2.38/1.03  --dbg_dump_prop_clauses                 false
% 2.38/1.03  --dbg_dump_prop_clauses_file            -
% 2.38/1.03  --dbg_out_stat                          false
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  ------ Proving...
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  % SZS status Theorem for theBenchmark.p
% 2.38/1.03  
% 2.38/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.38/1.03  
% 2.38/1.03  fof(f7,conjecture,(
% 2.38/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.38/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.03  
% 2.38/1.03  fof(f8,negated_conjecture,(
% 2.38/1.03    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.38/1.03    inference(negated_conjecture,[],[f7])).
% 2.38/1.03  
% 2.38/1.03  fof(f18,plain,(
% 2.38/1.03    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.38/1.03    inference(ennf_transformation,[],[f8])).
% 2.38/1.03  
% 2.38/1.03  fof(f19,plain,(
% 2.38/1.03    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.38/1.03    inference(flattening,[],[f18])).
% 2.38/1.03  
% 2.38/1.03  fof(f21,plain,(
% 2.38/1.03    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(sK1) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 2.38/1.03    introduced(choice_axiom,[])).
% 2.38/1.03  
% 2.38/1.03  fof(f20,plain,(
% 2.38/1.03    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k2_relat_1(sK0) = k1_relat_1(X1) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.38/1.03    introduced(choice_axiom,[])).
% 2.38/1.03  
% 2.38/1.03  fof(f22,plain,(
% 2.38/1.03    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.38/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).
% 2.38/1.03  
% 2.38/1.03  fof(f34,plain,(
% 2.38/1.03    v1_relat_1(sK1)),
% 2.38/1.03    inference(cnf_transformation,[],[f22])).
% 2.38/1.03  
% 2.38/1.03  fof(f32,plain,(
% 2.38/1.03    v1_relat_1(sK0)),
% 2.38/1.03    inference(cnf_transformation,[],[f22])).
% 2.38/1.03  
% 2.38/1.03  fof(f5,axiom,(
% 2.38/1.03    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 2.38/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.03  
% 2.38/1.03  fof(f14,plain,(
% 2.38/1.03    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.38/1.03    inference(ennf_transformation,[],[f5])).
% 2.38/1.03  
% 2.38/1.03  fof(f15,plain,(
% 2.38/1.03    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.38/1.03    inference(flattening,[],[f14])).
% 2.38/1.03  
% 2.38/1.03  fof(f28,plain,(
% 2.38/1.03    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.38/1.03    inference(cnf_transformation,[],[f15])).
% 2.38/1.03  
% 2.38/1.03  fof(f36,plain,(
% 2.38/1.03    v2_funct_1(sK0)),
% 2.38/1.03    inference(cnf_transformation,[],[f22])).
% 2.38/1.03  
% 2.38/1.03  fof(f33,plain,(
% 2.38/1.03    v1_funct_1(sK0)),
% 2.38/1.03    inference(cnf_transformation,[],[f22])).
% 2.38/1.03  
% 2.38/1.03  fof(f2,axiom,(
% 2.38/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 2.38/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.03  
% 2.38/1.03  fof(f10,plain,(
% 2.38/1.03    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.38/1.03    inference(ennf_transformation,[],[f2])).
% 2.38/1.03  
% 2.38/1.03  fof(f25,plain,(
% 2.38/1.03    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.38/1.03    inference(cnf_transformation,[],[f10])).
% 2.38/1.03  
% 2.38/1.03  fof(f6,axiom,(
% 2.38/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.38/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.03  
% 2.38/1.03  fof(f16,plain,(
% 2.38/1.03    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.38/1.03    inference(ennf_transformation,[],[f6])).
% 2.38/1.03  
% 2.38/1.03  fof(f17,plain,(
% 2.38/1.03    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.38/1.03    inference(flattening,[],[f16])).
% 2.38/1.03  
% 2.38/1.03  fof(f31,plain,(
% 2.38/1.03    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.38/1.03    inference(cnf_transformation,[],[f17])).
% 2.38/1.03  
% 2.38/1.03  fof(f4,axiom,(
% 2.38/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.38/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.03  
% 2.38/1.03  fof(f12,plain,(
% 2.38/1.03    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.38/1.03    inference(ennf_transformation,[],[f4])).
% 2.38/1.03  
% 2.38/1.03  fof(f13,plain,(
% 2.38/1.03    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.38/1.03    inference(flattening,[],[f12])).
% 2.38/1.03  
% 2.38/1.03  fof(f27,plain,(
% 2.38/1.03    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.38/1.03    inference(cnf_transformation,[],[f13])).
% 2.38/1.03  
% 2.38/1.03  fof(f38,plain,(
% 2.38/1.03    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 2.38/1.03    inference(cnf_transformation,[],[f22])).
% 2.38/1.03  
% 2.38/1.03  fof(f3,axiom,(
% 2.38/1.03    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.38/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.03  
% 2.38/1.03  fof(f11,plain,(
% 2.38/1.03    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.38/1.03    inference(ennf_transformation,[],[f3])).
% 2.38/1.03  
% 2.38/1.03  fof(f26,plain,(
% 2.38/1.03    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.38/1.03    inference(cnf_transformation,[],[f11])).
% 2.38/1.03  
% 2.38/1.03  fof(f37,plain,(
% 2.38/1.03    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 2.38/1.03    inference(cnf_transformation,[],[f22])).
% 2.38/1.03  
% 2.38/1.03  fof(f30,plain,(
% 2.38/1.03    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.38/1.03    inference(cnf_transformation,[],[f17])).
% 2.38/1.03  
% 2.38/1.03  fof(f1,axiom,(
% 2.38/1.03    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.38/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.03  
% 2.38/1.03  fof(f9,plain,(
% 2.38/1.03    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.38/1.03    inference(ennf_transformation,[],[f1])).
% 2.38/1.03  
% 2.38/1.03  fof(f23,plain,(
% 2.38/1.03    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.38/1.03    inference(cnf_transformation,[],[f9])).
% 2.38/1.03  
% 2.38/1.03  fof(f39,plain,(
% 2.38/1.03    k2_funct_1(sK0) != sK1),
% 2.38/1.03    inference(cnf_transformation,[],[f22])).
% 2.38/1.03  
% 2.38/1.03  cnf(c_14,negated_conjecture,
% 2.38/1.03      ( v1_relat_1(sK1) ),
% 2.38/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_274,negated_conjecture,
% 2.38/1.03      ( v1_relat_1(sK1) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_433,plain,
% 2.38/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 2.38/1.03      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_16,negated_conjecture,
% 2.38/1.03      ( v1_relat_1(sK0) ),
% 2.38/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_273,negated_conjecture,
% 2.38/1.03      ( v1_relat_1(sK0) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_434,plain,
% 2.38/1.03      ( v1_relat_1(sK0) = iProver_top ),
% 2.38/1.03      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_6,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v2_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | v1_relat_1(k4_relat_1(X0)) ),
% 2.38/1.03      inference(cnf_transformation,[],[f28]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_12,negated_conjecture,
% 2.38/1.03      ( v2_funct_1(sK0) ),
% 2.38/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_177,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | v1_relat_1(k4_relat_1(X0))
% 2.38/1.03      | sK0 != X0 ),
% 2.38/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_178,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | v1_relat_1(k4_relat_1(sK0))
% 2.38/1.03      | ~ v1_relat_1(sK0) ),
% 2.38/1.03      inference(unflattening,[status(thm)],[c_177]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_15,negated_conjecture,
% 2.38/1.03      ( v1_funct_1(sK0) ),
% 2.38/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_29,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | ~ v2_funct_1(sK0)
% 2.38/1.03      | v1_relat_1(k4_relat_1(sK0))
% 2.38/1.03      | ~ v1_relat_1(sK0) ),
% 2.38/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_180,plain,
% 2.38/1.03      ( v1_relat_1(k4_relat_1(sK0)) ),
% 2.38/1.03      inference(global_propositional_subsumption,
% 2.38/1.03                [status(thm)],
% 2.38/1.03                [c_178,c_16,c_15,c_12,c_29]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_270,plain,
% 2.38/1.03      ( v1_relat_1(k4_relat_1(sK0)) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_180]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_435,plain,
% 2.38/1.03      ( v1_relat_1(k4_relat_1(sK0)) = iProver_top ),
% 2.38/1.03      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_2,plain,
% 2.38/1.03      ( ~ v1_relat_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X1)
% 2.38/1.03      | ~ v1_relat_1(X2)
% 2.38/1.03      | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
% 2.38/1.03      inference(cnf_transformation,[],[f25]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_279,plain,
% 2.38/1.03      ( ~ v1_relat_1(X0_39)
% 2.38/1.03      | ~ v1_relat_1(X1_39)
% 2.38/1.03      | ~ v1_relat_1(X2_39)
% 2.38/1.03      | k5_relat_1(k5_relat_1(X0_39,X2_39),X1_39) = k5_relat_1(X0_39,k5_relat_1(X2_39,X1_39)) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_431,plain,
% 2.38/1.03      ( k5_relat_1(k5_relat_1(X0_39,X1_39),X2_39) = k5_relat_1(X0_39,k5_relat_1(X1_39,X2_39))
% 2.38/1.03      | v1_relat_1(X0_39) != iProver_top
% 2.38/1.03      | v1_relat_1(X1_39) != iProver_top
% 2.38/1.03      | v1_relat_1(X2_39) != iProver_top ),
% 2.38/1.03      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_964,plain,
% 2.38/1.03      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0_39,X1_39)) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0_39),X1_39)
% 2.38/1.03      | v1_relat_1(X0_39) != iProver_top
% 2.38/1.03      | v1_relat_1(X1_39) != iProver_top ),
% 2.38/1.03      inference(superposition,[status(thm)],[c_435,c_431]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_1531,plain,
% 2.38/1.03      ( k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),X0_39) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0_39))
% 2.38/1.03      | v1_relat_1(X0_39) != iProver_top ),
% 2.38/1.03      inference(superposition,[status(thm)],[c_434,c_964]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_7,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v2_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 2.38/1.03      inference(cnf_transformation,[],[f31]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_169,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 2.38/1.03      | sK0 != X0 ),
% 2.38/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_170,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | ~ v1_relat_1(sK0)
% 2.38/1.03      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.38/1.03      inference(unflattening,[status(thm)],[c_169]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_26,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | ~ v2_funct_1(sK0)
% 2.38/1.03      | ~ v1_relat_1(sK0)
% 2.38/1.03      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.38/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_172,plain,
% 2.38/1.03      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.38/1.03      inference(global_propositional_subsumption,
% 2.38/1.03                [status(thm)],
% 2.38/1.03                [c_170,c_16,c_15,c_12,c_26]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_271,plain,
% 2.38/1.03      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_172]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_4,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v2_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.38/1.03      inference(cnf_transformation,[],[f27]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_199,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.38/1.03      | sK0 != X0 ),
% 2.38/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_12]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_200,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | ~ v1_relat_1(sK0)
% 2.38/1.03      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.38/1.03      inference(unflattening,[status(thm)],[c_199]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_35,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | ~ v2_funct_1(sK0)
% 2.38/1.03      | ~ v1_relat_1(sK0)
% 2.38/1.03      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.38/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_202,plain,
% 2.38/1.03      ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.38/1.03      inference(global_propositional_subsumption,
% 2.38/1.03                [status(thm)],
% 2.38/1.03                [c_200,c_16,c_15,c_12,c_35]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_269,plain,
% 2.38/1.03      ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_202]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_456,plain,
% 2.38/1.03      ( k5_relat_1(k4_relat_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.38/1.03      inference(light_normalisation,[status(thm)],[c_271,c_269]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_1539,plain,
% 2.38/1.03      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0_39)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0_39)
% 2.38/1.03      | v1_relat_1(X0_39) != iProver_top ),
% 2.38/1.03      inference(light_normalisation,[status(thm)],[c_1531,c_456]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_2306,plain,
% 2.38/1.03      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
% 2.38/1.03      inference(superposition,[status(thm)],[c_433,c_1539]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_10,negated_conjecture,
% 2.38/1.03      ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.38/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_276,negated_conjecture,
% 2.38/1.03      ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_3,plain,
% 2.38/1.03      ( ~ v1_relat_1(X0)
% 2.38/1.03      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 2.38/1.03      inference(cnf_transformation,[],[f26]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_278,plain,
% 2.38/1.03      ( ~ v1_relat_1(X0_39)
% 2.38/1.03      | k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39 ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_432,plain,
% 2.38/1.03      ( k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39
% 2.38/1.03      | v1_relat_1(X0_39) != iProver_top ),
% 2.38/1.03      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_662,plain,
% 2.38/1.03      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
% 2.38/1.03      inference(superposition,[status(thm)],[c_433,c_432]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_11,negated_conjecture,
% 2.38/1.03      ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
% 2.38/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_275,negated_conjecture,
% 2.38/1.03      ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_670,plain,
% 2.38/1.03      ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = sK1 ),
% 2.38/1.03      inference(light_normalisation,[status(thm)],[c_662,c_275]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_2315,plain,
% 2.38/1.03      ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = sK1 ),
% 2.38/1.03      inference(light_normalisation,[status(thm)],[c_2306,c_276,c_670]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_2308,plain,
% 2.38/1.03      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,k4_relat_1(sK0))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
% 2.38/1.03      inference(superposition,[status(thm)],[c_435,c_1539]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_8,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v2_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 2.38/1.03      inference(cnf_transformation,[],[f30]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_161,plain,
% 2.38/1.03      ( ~ v1_funct_1(X0)
% 2.38/1.03      | ~ v1_relat_1(X0)
% 2.38/1.03      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 2.38/1.03      | sK0 != X0 ),
% 2.38/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_162,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | ~ v1_relat_1(sK0)
% 2.38/1.03      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.38/1.03      inference(unflattening,[status(thm)],[c_161]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_23,plain,
% 2.38/1.03      ( ~ v1_funct_1(sK0)
% 2.38/1.03      | ~ v2_funct_1(sK0)
% 2.38/1.03      | ~ v1_relat_1(sK0)
% 2.38/1.03      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.38/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_164,plain,
% 2.38/1.03      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.38/1.03      inference(global_propositional_subsumption,
% 2.38/1.03                [status(thm)],
% 2.38/1.03                [c_162,c_16,c_15,c_12,c_23]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_272,plain,
% 2.38/1.03      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_164]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_453,plain,
% 2.38/1.03      ( k5_relat_1(sK0,k4_relat_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.38/1.03      inference(light_normalisation,[status(thm)],[c_272,c_269]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_664,plain,
% 2.38/1.03      ( k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
% 2.38/1.03      inference(superposition,[status(thm)],[c_435,c_432]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_1,plain,
% 2.38/1.03      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.38/1.03      inference(cnf_transformation,[],[f23]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_280,plain,
% 2.38/1.03      ( ~ v1_relat_1(X0_39)
% 2.38/1.03      | k1_relat_1(k4_relat_1(X0_39)) = k2_relat_1(X0_39) ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_430,plain,
% 2.38/1.03      ( k1_relat_1(k4_relat_1(X0_39)) = k2_relat_1(X0_39)
% 2.38/1.03      | v1_relat_1(X0_39) != iProver_top ),
% 2.38/1.03      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_651,plain,
% 2.38/1.03      ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
% 2.38/1.03      inference(superposition,[status(thm)],[c_434,c_430]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_955,plain,
% 2.38/1.03      ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
% 2.38/1.03      inference(light_normalisation,[status(thm)],[c_664,c_651]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_2310,plain,
% 2.38/1.03      ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k4_relat_1(sK0) ),
% 2.38/1.03      inference(light_normalisation,[status(thm)],[c_2308,c_453,c_955]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_2316,plain,
% 2.38/1.03      ( k4_relat_1(sK0) = sK1 ),
% 2.38/1.03      inference(demodulation,[status(thm)],[c_2315,c_2310]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_9,negated_conjecture,
% 2.38/1.03      ( k2_funct_1(sK0) != sK1 ),
% 2.38/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_277,negated_conjecture,
% 2.38/1.03      ( k2_funct_1(sK0) != sK1 ),
% 2.38/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(c_447,plain,
% 2.38/1.03      ( k4_relat_1(sK0) != sK1 ),
% 2.38/1.03      inference(demodulation,[status(thm)],[c_269,c_277]) ).
% 2.38/1.03  
% 2.38/1.03  cnf(contradiction,plain,
% 2.38/1.03      ( $false ),
% 2.38/1.03      inference(minisat,[status(thm)],[c_2316,c_447]) ).
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.38/1.03  
% 2.38/1.03  ------                               Statistics
% 2.38/1.03  
% 2.38/1.03  ------ General
% 2.38/1.03  
% 2.38/1.03  abstr_ref_over_cycles:                  0
% 2.38/1.03  abstr_ref_under_cycles:                 0
% 2.38/1.03  gc_basic_clause_elim:                   0
% 2.38/1.03  forced_gc_time:                         0
% 2.38/1.03  parsing_time:                           0.012
% 2.38/1.03  unif_index_cands_time:                  0.
% 2.38/1.03  unif_index_add_time:                    0.
% 2.38/1.03  orderings_time:                         0.
% 2.38/1.03  out_proof_time:                         0.013
% 2.38/1.03  total_time:                             0.095
% 2.38/1.03  num_of_symbols:                         44
% 2.38/1.03  num_of_terms:                           1676
% 2.38/1.03  
% 2.38/1.03  ------ Preprocessing
% 2.38/1.03  
% 2.38/1.03  num_of_splits:                          0
% 2.38/1.03  num_of_split_atoms:                     0
% 2.38/1.03  num_of_reused_defs:                     0
% 2.38/1.03  num_eq_ax_congr_red:                    1
% 2.38/1.03  num_of_sem_filtered_clauses:            1
% 2.38/1.03  num_of_subtypes:                        2
% 2.38/1.03  monotx_restored_types:                  0
% 2.38/1.03  sat_num_of_epr_types:                   0
% 2.38/1.03  sat_num_of_non_cyclic_types:            0
% 2.38/1.03  sat_guarded_non_collapsed_types:        1
% 2.38/1.03  num_pure_diseq_elim:                    0
% 2.38/1.03  simp_replaced_by:                       0
% 2.38/1.03  res_preprocessed:                       79
% 2.38/1.03  prep_upred:                             0
% 2.38/1.03  prep_unflattend:                        5
% 2.38/1.03  smt_new_axioms:                         0
% 2.38/1.03  pred_elim_cands:                        1
% 2.38/1.03  pred_elim:                              2
% 2.38/1.03  pred_elim_cl:                           4
% 2.38/1.03  pred_elim_cycles:                       4
% 2.38/1.03  merged_defs:                            0
% 2.38/1.03  merged_defs_ncl:                        0
% 2.38/1.03  bin_hyper_res:                          0
% 2.38/1.03  prep_cycles:                            4
% 2.38/1.03  pred_elim_time:                         0.
% 2.38/1.03  splitting_time:                         0.
% 2.38/1.03  sem_filter_time:                        0.
% 2.38/1.03  monotx_time:                            0.
% 2.38/1.03  subtype_inf_time:                       0.
% 2.38/1.03  
% 2.38/1.03  ------ Problem properties
% 2.38/1.03  
% 2.38/1.03  clauses:                                13
% 2.38/1.03  conjectures:                            5
% 2.38/1.03  epr:                                    2
% 2.38/1.03  horn:                                   13
% 2.38/1.03  ground:                                 9
% 2.38/1.03  unary:                                  9
% 2.38/1.03  binary:                                 3
% 2.38/1.03  lits:                                   19
% 2.38/1.03  lits_eq:                                10
% 2.38/1.03  fd_pure:                                0
% 2.38/1.03  fd_pseudo:                              0
% 2.38/1.03  fd_cond:                                0
% 2.38/1.03  fd_pseudo_cond:                         0
% 2.38/1.03  ac_symbols:                             0
% 2.38/1.03  
% 2.38/1.03  ------ Propositional Solver
% 2.38/1.03  
% 2.38/1.03  prop_solver_calls:                      31
% 2.38/1.03  prop_fast_solver_calls:                 385
% 2.38/1.03  smt_solver_calls:                       0
% 2.38/1.03  smt_fast_solver_calls:                  0
% 2.38/1.03  prop_num_of_clauses:                    767
% 2.38/1.03  prop_preprocess_simplified:             2388
% 2.38/1.03  prop_fo_subsumed:                       10
% 2.38/1.03  prop_solver_time:                       0.
% 2.38/1.03  smt_solver_time:                        0.
% 2.38/1.03  smt_fast_solver_time:                   0.
% 2.38/1.03  prop_fast_solver_time:                  0.
% 2.38/1.03  prop_unsat_core_time:                   0.
% 2.38/1.03  
% 2.38/1.03  ------ QBF
% 2.38/1.03  
% 2.38/1.03  qbf_q_res:                              0
% 2.38/1.03  qbf_num_tautologies:                    0
% 2.38/1.03  qbf_prep_cycles:                        0
% 2.38/1.03  
% 2.38/1.03  ------ BMC1
% 2.38/1.03  
% 2.38/1.03  bmc1_current_bound:                     -1
% 2.38/1.03  bmc1_last_solved_bound:                 -1
% 2.38/1.03  bmc1_unsat_core_size:                   -1
% 2.38/1.03  bmc1_unsat_core_parents_size:           -1
% 2.38/1.03  bmc1_merge_next_fun:                    0
% 2.38/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.38/1.03  
% 2.38/1.03  ------ Instantiation
% 2.38/1.03  
% 2.38/1.03  inst_num_of_clauses:                    411
% 2.38/1.03  inst_num_in_passive:                    84
% 2.38/1.03  inst_num_in_active:                     245
% 2.38/1.03  inst_num_in_unprocessed:                82
% 2.38/1.03  inst_num_of_loops:                      270
% 2.38/1.03  inst_num_of_learning_restarts:          0
% 2.38/1.03  inst_num_moves_active_passive:          15
% 2.38/1.03  inst_lit_activity:                      0
% 2.38/1.03  inst_lit_activity_moves:                0
% 2.38/1.03  inst_num_tautologies:                   0
% 2.38/1.03  inst_num_prop_implied:                  0
% 2.38/1.03  inst_num_existing_simplified:           0
% 2.38/1.03  inst_num_eq_res_simplified:             0
% 2.38/1.03  inst_num_child_elim:                    0
% 2.38/1.03  inst_num_of_dismatching_blockings:      86
% 2.38/1.03  inst_num_of_non_proper_insts:           488
% 2.38/1.03  inst_num_of_duplicates:                 0
% 2.38/1.03  inst_inst_num_from_inst_to_res:         0
% 2.38/1.03  inst_dismatching_checking_time:         0.
% 2.38/1.03  
% 2.38/1.03  ------ Resolution
% 2.38/1.03  
% 2.38/1.03  res_num_of_clauses:                     0
% 2.38/1.03  res_num_in_passive:                     0
% 2.38/1.03  res_num_in_active:                      0
% 2.38/1.03  res_num_of_loops:                       83
% 2.38/1.03  res_forward_subset_subsumed:            122
% 2.38/1.03  res_backward_subset_subsumed:           2
% 2.38/1.03  res_forward_subsumed:                   0
% 2.38/1.03  res_backward_subsumed:                  0
% 2.38/1.03  res_forward_subsumption_resolution:     0
% 2.38/1.03  res_backward_subsumption_resolution:    0
% 2.38/1.03  res_clause_to_clause_subsumption:       85
% 2.38/1.03  res_orphan_elimination:                 0
% 2.38/1.03  res_tautology_del:                      85
% 2.38/1.03  res_num_eq_res_simplified:              0
% 2.38/1.03  res_num_sel_changes:                    0
% 2.38/1.03  res_moves_from_active_to_pass:          0
% 2.38/1.03  
% 2.38/1.03  ------ Superposition
% 2.38/1.03  
% 2.38/1.03  sup_time_total:                         0.
% 2.38/1.03  sup_time_generating:                    0.
% 2.38/1.03  sup_time_sim_full:                      0.
% 2.38/1.03  sup_time_sim_immed:                     0.
% 2.38/1.03  
% 2.38/1.03  sup_num_of_clauses:                     56
% 2.38/1.03  sup_num_in_active:                      54
% 2.38/1.03  sup_num_in_passive:                     2
% 2.38/1.03  sup_num_of_loops:                       53
% 2.38/1.03  sup_fw_superposition:                   45
% 2.38/1.03  sup_bw_superposition:                   0
% 2.38/1.03  sup_immediate_simplified:               14
% 2.38/1.03  sup_given_eliminated:                   1
% 2.38/1.03  comparisons_done:                       0
% 2.38/1.03  comparisons_avoided:                    0
% 2.38/1.03  
% 2.38/1.03  ------ Simplifications
% 2.38/1.03  
% 2.38/1.03  
% 2.38/1.03  sim_fw_subset_subsumed:                 0
% 2.38/1.03  sim_bw_subset_subsumed:                 0
% 2.38/1.03  sim_fw_subsumed:                        0
% 2.38/1.03  sim_bw_subsumed:                        0
% 2.38/1.03  sim_fw_subsumption_res:                 0
% 2.38/1.03  sim_bw_subsumption_res:                 0
% 2.38/1.03  sim_tautology_del:                      0
% 2.38/1.03  sim_eq_tautology_del:                   0
% 2.38/1.03  sim_eq_res_simp:                        0
% 2.38/1.03  sim_fw_demodulated:                     0
% 2.38/1.03  sim_bw_demodulated:                     5
% 2.38/1.03  sim_light_normalised:                   21
% 2.38/1.03  sim_joinable_taut:                      0
% 2.38/1.03  sim_joinable_simp:                      0
% 2.38/1.03  sim_ac_normalised:                      0
% 2.38/1.03  sim_smt_subsumption:                    0
% 2.38/1.03  
%------------------------------------------------------------------------------
