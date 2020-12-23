%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:48 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 460 expanded)
%              Number of clauses        :   63 ( 136 expanded)
%              Number of leaves         :    8 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  285 (2799 expanded)
%              Number of equality atoms :  134 (1109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f19,plain,(
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

fof(f18,plain,
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

fof(f20,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    & k1_relat_1(sK1) = k2_relat_1(sK0)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_248,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_430,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_254,plain,
    ( ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X0_39)
    | v1_relat_1(k2_funct_1(X0_39)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_427,plain,
    ( v1_funct_1(X0_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k2_funct_1(X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_247,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_431,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_257,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X2_39)
    | k5_relat_1(k5_relat_1(X2_39,X1_39),X0_39) = k5_relat_1(X2_39,k5_relat_1(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_424,plain,
    ( k5_relat_1(k5_relat_1(X0_39,X1_39),X2_39) = k5_relat_1(X0_39,k5_relat_1(X1_39,X2_39))
    | v1_relat_1(X2_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_927,plain,
    ( k5_relat_1(k2_funct_1(X0_39),k5_relat_1(X1_39,X2_39)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_39),X1_39),X2_39)
    | v1_funct_1(X0_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X2_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_427,c_424])).

cnf(c_1664,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0_39),X1_39) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0_39,X1_39))
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_927])).

cnf(c_16,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3243,plain,
    ( v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0_39),X1_39) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0_39,X1_39)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_16])).

cnf(c_3244,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0_39),X1_39) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0_39,X1_39))
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(renaming,[status(thm)],[c_3243])).

cnf(c_3251,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0_39)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_3244])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_156,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_157,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_25,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_159,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_157,c_15,c_14,c_11,c_25])).

cnf(c_245,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_159])).

cnf(c_10,negated_conjecture,
    ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_251,negated_conjecture,
    ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_453,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_245,c_251])).

cnf(c_3263,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0_39)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3251,c_453])).

cnf(c_3284,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,k2_funct_1(X0_39))) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(X0_39))
    | v1_funct_1(X0_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_427,c_3263])).

cnf(c_3837,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(sK0))
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_3284])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_148,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_149,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_22,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_151,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_149,c_15,c_14,c_11,c_22])).

cnf(c_246,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_151])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_256,plain,
    ( ~ v1_relat_1(X0_39)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_425,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_774,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(X0_39))),k2_funct_1(X0_39)) = k2_funct_1(X0_39)
    | v1_funct_1(X0_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_427,c_425])).

cnf(c_838,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_430,c_774])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_164,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_165,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_164])).

cnf(c_28,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_167,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_165,c_15,c_14,c_11,c_28])).

cnf(c_244,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_444,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_244,c_251])).

cnf(c_850,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(sK0)) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_838,c_444])).

cnf(c_863,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(sK0)) = k2_funct_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_16])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_249,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_429,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_3282,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_429,c_3263])).

cnf(c_9,negated_conjecture,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_252,negated_conjecture,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_632,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_429,c_425])).

cnf(c_3294,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3282,c_252,c_632])).

cnf(c_3849,plain,
    ( k2_funct_1(sK0) = sK1
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3837,c_246,c_863,c_3294])).

cnf(c_8,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_253,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3849,c_253,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.65/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.00  
% 2.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/1.00  
% 2.65/1.00  ------  iProver source info
% 2.65/1.00  
% 2.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/1.00  git: non_committed_changes: false
% 2.65/1.00  git: last_make_outside_of_git: false
% 2.65/1.00  
% 2.65/1.00  ------ 
% 2.65/1.00  
% 2.65/1.00  ------ Input Options
% 2.65/1.00  
% 2.65/1.00  --out_options                           all
% 2.65/1.00  --tptp_safe_out                         true
% 2.65/1.00  --problem_path                          ""
% 2.65/1.00  --include_path                          ""
% 2.65/1.00  --clausifier                            res/vclausify_rel
% 2.65/1.00  --clausifier_options                    --mode clausify
% 2.65/1.00  --stdin                                 false
% 2.65/1.00  --stats_out                             all
% 2.65/1.00  
% 2.65/1.00  ------ General Options
% 2.65/1.00  
% 2.65/1.00  --fof                                   false
% 2.65/1.00  --time_out_real                         305.
% 2.65/1.00  --time_out_virtual                      -1.
% 2.65/1.00  --symbol_type_check                     false
% 2.65/1.00  --clausify_out                          false
% 2.65/1.00  --sig_cnt_out                           false
% 2.65/1.00  --trig_cnt_out                          false
% 2.65/1.00  --trig_cnt_out_tolerance                1.
% 2.65/1.00  --trig_cnt_out_sk_spl                   false
% 2.65/1.00  --abstr_cl_out                          false
% 2.65/1.00  
% 2.65/1.00  ------ Global Options
% 2.65/1.00  
% 2.65/1.00  --schedule                              default
% 2.65/1.00  --add_important_lit                     false
% 2.65/1.00  --prop_solver_per_cl                    1000
% 2.65/1.00  --min_unsat_core                        false
% 2.65/1.00  --soft_assumptions                      false
% 2.65/1.00  --soft_lemma_size                       3
% 2.65/1.00  --prop_impl_unit_size                   0
% 2.65/1.00  --prop_impl_unit                        []
% 2.65/1.00  --share_sel_clauses                     true
% 2.65/1.00  --reset_solvers                         false
% 2.65/1.00  --bc_imp_inh                            [conj_cone]
% 2.65/1.00  --conj_cone_tolerance                   3.
% 2.65/1.00  --extra_neg_conj                        none
% 2.65/1.00  --large_theory_mode                     true
% 2.65/1.00  --prolific_symb_bound                   200
% 2.65/1.00  --lt_threshold                          2000
% 2.65/1.00  --clause_weak_htbl                      true
% 2.65/1.00  --gc_record_bc_elim                     false
% 2.65/1.00  
% 2.65/1.00  ------ Preprocessing Options
% 2.65/1.00  
% 2.65/1.00  --preprocessing_flag                    true
% 2.65/1.00  --time_out_prep_mult                    0.1
% 2.65/1.00  --splitting_mode                        input
% 2.65/1.00  --splitting_grd                         true
% 2.65/1.00  --splitting_cvd                         false
% 2.65/1.00  --splitting_cvd_svl                     false
% 2.65/1.00  --splitting_nvd                         32
% 2.65/1.00  --sub_typing                            true
% 2.65/1.00  --prep_gs_sim                           true
% 2.65/1.00  --prep_unflatten                        true
% 2.65/1.00  --prep_res_sim                          true
% 2.65/1.00  --prep_upred                            true
% 2.65/1.00  --prep_sem_filter                       exhaustive
% 2.65/1.00  --prep_sem_filter_out                   false
% 2.65/1.00  --pred_elim                             true
% 2.65/1.00  --res_sim_input                         true
% 2.65/1.00  --eq_ax_congr_red                       true
% 2.65/1.00  --pure_diseq_elim                       true
% 2.65/1.00  --brand_transform                       false
% 2.65/1.00  --non_eq_to_eq                          false
% 2.65/1.00  --prep_def_merge                        true
% 2.65/1.00  --prep_def_merge_prop_impl              false
% 2.65/1.00  --prep_def_merge_mbd                    true
% 2.65/1.00  --prep_def_merge_tr_red                 false
% 2.65/1.00  --prep_def_merge_tr_cl                  false
% 2.65/1.00  --smt_preprocessing                     true
% 2.65/1.00  --smt_ac_axioms                         fast
% 2.65/1.00  --preprocessed_out                      false
% 2.65/1.00  --preprocessed_stats                    false
% 2.65/1.00  
% 2.65/1.00  ------ Abstraction refinement Options
% 2.65/1.00  
% 2.65/1.00  --abstr_ref                             []
% 2.65/1.00  --abstr_ref_prep                        false
% 2.65/1.00  --abstr_ref_until_sat                   false
% 2.65/1.00  --abstr_ref_sig_restrict                funpre
% 2.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/1.00  --abstr_ref_under                       []
% 2.65/1.00  
% 2.65/1.00  ------ SAT Options
% 2.65/1.00  
% 2.65/1.00  --sat_mode                              false
% 2.65/1.00  --sat_fm_restart_options                ""
% 2.65/1.00  --sat_gr_def                            false
% 2.65/1.00  --sat_epr_types                         true
% 2.65/1.00  --sat_non_cyclic_types                  false
% 2.65/1.00  --sat_finite_models                     false
% 2.65/1.00  --sat_fm_lemmas                         false
% 2.65/1.00  --sat_fm_prep                           false
% 2.65/1.00  --sat_fm_uc_incr                        true
% 2.65/1.00  --sat_out_model                         small
% 2.65/1.00  --sat_out_clauses                       false
% 2.65/1.00  
% 2.65/1.00  ------ QBF Options
% 2.65/1.00  
% 2.65/1.00  --qbf_mode                              false
% 2.65/1.00  --qbf_elim_univ                         false
% 2.65/1.00  --qbf_dom_inst                          none
% 2.65/1.00  --qbf_dom_pre_inst                      false
% 2.65/1.00  --qbf_sk_in                             false
% 2.65/1.00  --qbf_pred_elim                         true
% 2.65/1.00  --qbf_split                             512
% 2.65/1.00  
% 2.65/1.00  ------ BMC1 Options
% 2.65/1.00  
% 2.65/1.00  --bmc1_incremental                      false
% 2.65/1.00  --bmc1_axioms                           reachable_all
% 2.65/1.00  --bmc1_min_bound                        0
% 2.65/1.00  --bmc1_max_bound                        -1
% 2.65/1.00  --bmc1_max_bound_default                -1
% 2.65/1.00  --bmc1_symbol_reachability              true
% 2.65/1.00  --bmc1_property_lemmas                  false
% 2.65/1.00  --bmc1_k_induction                      false
% 2.65/1.00  --bmc1_non_equiv_states                 false
% 2.65/1.00  --bmc1_deadlock                         false
% 2.65/1.00  --bmc1_ucm                              false
% 2.65/1.00  --bmc1_add_unsat_core                   none
% 2.65/1.00  --bmc1_unsat_core_children              false
% 2.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/1.00  --bmc1_out_stat                         full
% 2.65/1.00  --bmc1_ground_init                      false
% 2.65/1.00  --bmc1_pre_inst_next_state              false
% 2.65/1.00  --bmc1_pre_inst_state                   false
% 2.65/1.00  --bmc1_pre_inst_reach_state             false
% 2.65/1.00  --bmc1_out_unsat_core                   false
% 2.65/1.00  --bmc1_aig_witness_out                  false
% 2.65/1.00  --bmc1_verbose                          false
% 2.65/1.00  --bmc1_dump_clauses_tptp                false
% 2.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.65/1.00  --bmc1_dump_file                        -
% 2.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.65/1.00  --bmc1_ucm_extend_mode                  1
% 2.65/1.00  --bmc1_ucm_init_mode                    2
% 2.65/1.00  --bmc1_ucm_cone_mode                    none
% 2.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.65/1.00  --bmc1_ucm_relax_model                  4
% 2.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/1.00  --bmc1_ucm_layered_model                none
% 2.65/1.00  --bmc1_ucm_max_lemma_size               10
% 2.65/1.00  
% 2.65/1.00  ------ AIG Options
% 2.65/1.00  
% 2.65/1.00  --aig_mode                              false
% 2.65/1.00  
% 2.65/1.00  ------ Instantiation Options
% 2.65/1.00  
% 2.65/1.00  --instantiation_flag                    true
% 2.65/1.00  --inst_sos_flag                         false
% 2.65/1.00  --inst_sos_phase                        true
% 2.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/1.00  --inst_lit_sel_side                     num_symb
% 2.65/1.00  --inst_solver_per_active                1400
% 2.65/1.00  --inst_solver_calls_frac                1.
% 2.65/1.00  --inst_passive_queue_type               priority_queues
% 2.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/1.00  --inst_passive_queues_freq              [25;2]
% 2.65/1.00  --inst_dismatching                      true
% 2.65/1.00  --inst_eager_unprocessed_to_passive     true
% 2.65/1.00  --inst_prop_sim_given                   true
% 2.65/1.00  --inst_prop_sim_new                     false
% 2.65/1.00  --inst_subs_new                         false
% 2.65/1.00  --inst_eq_res_simp                      false
% 2.65/1.00  --inst_subs_given                       false
% 2.65/1.00  --inst_orphan_elimination               true
% 2.65/1.00  --inst_learning_loop_flag               true
% 2.65/1.00  --inst_learning_start                   3000
% 2.65/1.00  --inst_learning_factor                  2
% 2.65/1.00  --inst_start_prop_sim_after_learn       3
% 2.65/1.00  --inst_sel_renew                        solver
% 2.65/1.00  --inst_lit_activity_flag                true
% 2.65/1.00  --inst_restr_to_given                   false
% 2.65/1.00  --inst_activity_threshold               500
% 2.65/1.00  --inst_out_proof                        true
% 2.65/1.00  
% 2.65/1.00  ------ Resolution Options
% 2.65/1.00  
% 2.65/1.00  --resolution_flag                       true
% 2.65/1.00  --res_lit_sel                           adaptive
% 2.65/1.00  --res_lit_sel_side                      none
% 2.65/1.00  --res_ordering                          kbo
% 2.65/1.00  --res_to_prop_solver                    active
% 2.65/1.00  --res_prop_simpl_new                    false
% 2.65/1.00  --res_prop_simpl_given                  true
% 2.65/1.00  --res_passive_queue_type                priority_queues
% 2.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/1.00  --res_passive_queues_freq               [15;5]
% 2.65/1.00  --res_forward_subs                      full
% 2.65/1.00  --res_backward_subs                     full
% 2.65/1.00  --res_forward_subs_resolution           true
% 2.65/1.00  --res_backward_subs_resolution          true
% 2.65/1.00  --res_orphan_elimination                true
% 2.65/1.00  --res_time_limit                        2.
% 2.65/1.00  --res_out_proof                         true
% 2.65/1.00  
% 2.65/1.00  ------ Superposition Options
% 2.65/1.00  
% 2.65/1.00  --superposition_flag                    true
% 2.65/1.00  --sup_passive_queue_type                priority_queues
% 2.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.65/1.00  --demod_completeness_check              fast
% 2.65/1.00  --demod_use_ground                      true
% 2.65/1.00  --sup_to_prop_solver                    passive
% 2.65/1.00  --sup_prop_simpl_new                    true
% 2.65/1.00  --sup_prop_simpl_given                  true
% 2.65/1.00  --sup_fun_splitting                     false
% 2.65/1.00  --sup_smt_interval                      50000
% 2.65/1.00  
% 2.65/1.00  ------ Superposition Simplification Setup
% 2.65/1.00  
% 2.65/1.00  --sup_indices_passive                   []
% 2.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.00  --sup_full_bw                           [BwDemod]
% 2.65/1.00  --sup_immed_triv                        [TrivRules]
% 2.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.00  --sup_immed_bw_main                     []
% 2.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.00  
% 2.65/1.00  ------ Combination Options
% 2.65/1.00  
% 2.65/1.00  --comb_res_mult                         3
% 2.65/1.00  --comb_sup_mult                         2
% 2.65/1.00  --comb_inst_mult                        10
% 2.65/1.00  
% 2.65/1.00  ------ Debug Options
% 2.65/1.00  
% 2.65/1.00  --dbg_backtrace                         false
% 2.65/1.00  --dbg_dump_prop_clauses                 false
% 2.65/1.00  --dbg_dump_prop_clauses_file            -
% 2.65/1.00  --dbg_out_stat                          false
% 2.65/1.00  ------ Parsing...
% 2.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/1.00  
% 2.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.65/1.00  
% 2.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/1.00  
% 2.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/1.00  ------ Proving...
% 2.65/1.00  ------ Problem Properties 
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  clauses                                 15
% 2.65/1.00  conjectures                             7
% 2.65/1.00  EPR                                     4
% 2.65/1.00  Horn                                    15
% 2.65/1.00  unary                                   11
% 2.65/1.00  binary                                  1
% 2.65/1.00  lits                                    23
% 2.65/1.00  lits eq                                 9
% 2.65/1.00  fd_pure                                 0
% 2.65/1.00  fd_pseudo                               0
% 2.65/1.00  fd_cond                                 0
% 2.65/1.00  fd_pseudo_cond                          0
% 2.65/1.00  AC symbols                              0
% 2.65/1.00  
% 2.65/1.00  ------ Schedule dynamic 5 is on 
% 2.65/1.00  
% 2.65/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  ------ 
% 2.65/1.00  Current options:
% 2.65/1.00  ------ 
% 2.65/1.00  
% 2.65/1.00  ------ Input Options
% 2.65/1.00  
% 2.65/1.00  --out_options                           all
% 2.65/1.00  --tptp_safe_out                         true
% 2.65/1.00  --problem_path                          ""
% 2.65/1.00  --include_path                          ""
% 2.65/1.00  --clausifier                            res/vclausify_rel
% 2.65/1.00  --clausifier_options                    --mode clausify
% 2.65/1.00  --stdin                                 false
% 2.65/1.00  --stats_out                             all
% 2.65/1.00  
% 2.65/1.00  ------ General Options
% 2.65/1.00  
% 2.65/1.00  --fof                                   false
% 2.65/1.00  --time_out_real                         305.
% 2.65/1.00  --time_out_virtual                      -1.
% 2.65/1.00  --symbol_type_check                     false
% 2.65/1.00  --clausify_out                          false
% 2.65/1.00  --sig_cnt_out                           false
% 2.65/1.00  --trig_cnt_out                          false
% 2.65/1.00  --trig_cnt_out_tolerance                1.
% 2.65/1.00  --trig_cnt_out_sk_spl                   false
% 2.65/1.00  --abstr_cl_out                          false
% 2.65/1.00  
% 2.65/1.00  ------ Global Options
% 2.65/1.00  
% 2.65/1.00  --schedule                              default
% 2.65/1.00  --add_important_lit                     false
% 2.65/1.00  --prop_solver_per_cl                    1000
% 2.65/1.00  --min_unsat_core                        false
% 2.65/1.00  --soft_assumptions                      false
% 2.65/1.00  --soft_lemma_size                       3
% 2.65/1.00  --prop_impl_unit_size                   0
% 2.65/1.00  --prop_impl_unit                        []
% 2.65/1.00  --share_sel_clauses                     true
% 2.65/1.00  --reset_solvers                         false
% 2.65/1.00  --bc_imp_inh                            [conj_cone]
% 2.65/1.00  --conj_cone_tolerance                   3.
% 2.65/1.00  --extra_neg_conj                        none
% 2.65/1.00  --large_theory_mode                     true
% 2.65/1.00  --prolific_symb_bound                   200
% 2.65/1.00  --lt_threshold                          2000
% 2.65/1.00  --clause_weak_htbl                      true
% 2.65/1.00  --gc_record_bc_elim                     false
% 2.65/1.00  
% 2.65/1.00  ------ Preprocessing Options
% 2.65/1.00  
% 2.65/1.00  --preprocessing_flag                    true
% 2.65/1.00  --time_out_prep_mult                    0.1
% 2.65/1.00  --splitting_mode                        input
% 2.65/1.00  --splitting_grd                         true
% 2.65/1.00  --splitting_cvd                         false
% 2.65/1.00  --splitting_cvd_svl                     false
% 2.65/1.00  --splitting_nvd                         32
% 2.65/1.00  --sub_typing                            true
% 2.65/1.00  --prep_gs_sim                           true
% 2.65/1.00  --prep_unflatten                        true
% 2.65/1.00  --prep_res_sim                          true
% 2.65/1.00  --prep_upred                            true
% 2.65/1.00  --prep_sem_filter                       exhaustive
% 2.65/1.00  --prep_sem_filter_out                   false
% 2.65/1.00  --pred_elim                             true
% 2.65/1.00  --res_sim_input                         true
% 2.65/1.00  --eq_ax_congr_red                       true
% 2.65/1.00  --pure_diseq_elim                       true
% 2.65/1.00  --brand_transform                       false
% 2.65/1.00  --non_eq_to_eq                          false
% 2.65/1.00  --prep_def_merge                        true
% 2.65/1.00  --prep_def_merge_prop_impl              false
% 2.65/1.00  --prep_def_merge_mbd                    true
% 2.65/1.00  --prep_def_merge_tr_red                 false
% 2.65/1.00  --prep_def_merge_tr_cl                  false
% 2.65/1.00  --smt_preprocessing                     true
% 2.65/1.00  --smt_ac_axioms                         fast
% 2.65/1.00  --preprocessed_out                      false
% 2.65/1.00  --preprocessed_stats                    false
% 2.65/1.00  
% 2.65/1.00  ------ Abstraction refinement Options
% 2.65/1.00  
% 2.65/1.00  --abstr_ref                             []
% 2.65/1.00  --abstr_ref_prep                        false
% 2.65/1.00  --abstr_ref_until_sat                   false
% 2.65/1.00  --abstr_ref_sig_restrict                funpre
% 2.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/1.00  --abstr_ref_under                       []
% 2.65/1.00  
% 2.65/1.00  ------ SAT Options
% 2.65/1.00  
% 2.65/1.00  --sat_mode                              false
% 2.65/1.00  --sat_fm_restart_options                ""
% 2.65/1.00  --sat_gr_def                            false
% 2.65/1.00  --sat_epr_types                         true
% 2.65/1.00  --sat_non_cyclic_types                  false
% 2.65/1.00  --sat_finite_models                     false
% 2.65/1.00  --sat_fm_lemmas                         false
% 2.65/1.00  --sat_fm_prep                           false
% 2.65/1.00  --sat_fm_uc_incr                        true
% 2.65/1.00  --sat_out_model                         small
% 2.65/1.00  --sat_out_clauses                       false
% 2.65/1.00  
% 2.65/1.00  ------ QBF Options
% 2.65/1.00  
% 2.65/1.00  --qbf_mode                              false
% 2.65/1.00  --qbf_elim_univ                         false
% 2.65/1.00  --qbf_dom_inst                          none
% 2.65/1.00  --qbf_dom_pre_inst                      false
% 2.65/1.00  --qbf_sk_in                             false
% 2.65/1.00  --qbf_pred_elim                         true
% 2.65/1.00  --qbf_split                             512
% 2.65/1.00  
% 2.65/1.00  ------ BMC1 Options
% 2.65/1.00  
% 2.65/1.00  --bmc1_incremental                      false
% 2.65/1.00  --bmc1_axioms                           reachable_all
% 2.65/1.00  --bmc1_min_bound                        0
% 2.65/1.00  --bmc1_max_bound                        -1
% 2.65/1.00  --bmc1_max_bound_default                -1
% 2.65/1.00  --bmc1_symbol_reachability              true
% 2.65/1.00  --bmc1_property_lemmas                  false
% 2.65/1.00  --bmc1_k_induction                      false
% 2.65/1.00  --bmc1_non_equiv_states                 false
% 2.65/1.00  --bmc1_deadlock                         false
% 2.65/1.00  --bmc1_ucm                              false
% 2.65/1.00  --bmc1_add_unsat_core                   none
% 2.65/1.00  --bmc1_unsat_core_children              false
% 2.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/1.00  --bmc1_out_stat                         full
% 2.65/1.00  --bmc1_ground_init                      false
% 2.65/1.00  --bmc1_pre_inst_next_state              false
% 2.65/1.00  --bmc1_pre_inst_state                   false
% 2.65/1.00  --bmc1_pre_inst_reach_state             false
% 2.65/1.00  --bmc1_out_unsat_core                   false
% 2.65/1.00  --bmc1_aig_witness_out                  false
% 2.65/1.00  --bmc1_verbose                          false
% 2.65/1.00  --bmc1_dump_clauses_tptp                false
% 2.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.65/1.00  --bmc1_dump_file                        -
% 2.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.65/1.00  --bmc1_ucm_extend_mode                  1
% 2.65/1.00  --bmc1_ucm_init_mode                    2
% 2.65/1.00  --bmc1_ucm_cone_mode                    none
% 2.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.65/1.00  --bmc1_ucm_relax_model                  4
% 2.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/1.00  --bmc1_ucm_layered_model                none
% 2.65/1.00  --bmc1_ucm_max_lemma_size               10
% 2.65/1.00  
% 2.65/1.00  ------ AIG Options
% 2.65/1.00  
% 2.65/1.00  --aig_mode                              false
% 2.65/1.00  
% 2.65/1.00  ------ Instantiation Options
% 2.65/1.00  
% 2.65/1.00  --instantiation_flag                    true
% 2.65/1.00  --inst_sos_flag                         false
% 2.65/1.00  --inst_sos_phase                        true
% 2.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/1.00  --inst_lit_sel_side                     none
% 2.65/1.00  --inst_solver_per_active                1400
% 2.65/1.00  --inst_solver_calls_frac                1.
% 2.65/1.00  --inst_passive_queue_type               priority_queues
% 2.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/1.00  --inst_passive_queues_freq              [25;2]
% 2.65/1.00  --inst_dismatching                      true
% 2.65/1.00  --inst_eager_unprocessed_to_passive     true
% 2.65/1.00  --inst_prop_sim_given                   true
% 2.65/1.00  --inst_prop_sim_new                     false
% 2.65/1.00  --inst_subs_new                         false
% 2.65/1.00  --inst_eq_res_simp                      false
% 2.65/1.00  --inst_subs_given                       false
% 2.65/1.00  --inst_orphan_elimination               true
% 2.65/1.00  --inst_learning_loop_flag               true
% 2.65/1.00  --inst_learning_start                   3000
% 2.65/1.00  --inst_learning_factor                  2
% 2.65/1.00  --inst_start_prop_sim_after_learn       3
% 2.65/1.00  --inst_sel_renew                        solver
% 2.65/1.00  --inst_lit_activity_flag                true
% 2.65/1.00  --inst_restr_to_given                   false
% 2.65/1.00  --inst_activity_threshold               500
% 2.65/1.00  --inst_out_proof                        true
% 2.65/1.00  
% 2.65/1.00  ------ Resolution Options
% 2.65/1.00  
% 2.65/1.00  --resolution_flag                       false
% 2.65/1.00  --res_lit_sel                           adaptive
% 2.65/1.00  --res_lit_sel_side                      none
% 2.65/1.00  --res_ordering                          kbo
% 2.65/1.00  --res_to_prop_solver                    active
% 2.65/1.00  --res_prop_simpl_new                    false
% 2.65/1.00  --res_prop_simpl_given                  true
% 2.65/1.00  --res_passive_queue_type                priority_queues
% 2.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/1.00  --res_passive_queues_freq               [15;5]
% 2.65/1.00  --res_forward_subs                      full
% 2.65/1.00  --res_backward_subs                     full
% 2.65/1.00  --res_forward_subs_resolution           true
% 2.65/1.00  --res_backward_subs_resolution          true
% 2.65/1.00  --res_orphan_elimination                true
% 2.65/1.00  --res_time_limit                        2.
% 2.65/1.00  --res_out_proof                         true
% 2.65/1.00  
% 2.65/1.00  ------ Superposition Options
% 2.65/1.00  
% 2.65/1.00  --superposition_flag                    true
% 2.65/1.00  --sup_passive_queue_type                priority_queues
% 2.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.65/1.00  --demod_completeness_check              fast
% 2.65/1.00  --demod_use_ground                      true
% 2.65/1.00  --sup_to_prop_solver                    passive
% 2.65/1.00  --sup_prop_simpl_new                    true
% 2.65/1.00  --sup_prop_simpl_given                  true
% 2.65/1.00  --sup_fun_splitting                     false
% 2.65/1.00  --sup_smt_interval                      50000
% 2.65/1.00  
% 2.65/1.00  ------ Superposition Simplification Setup
% 2.65/1.00  
% 2.65/1.00  --sup_indices_passive                   []
% 2.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.00  --sup_full_bw                           [BwDemod]
% 2.65/1.00  --sup_immed_triv                        [TrivRules]
% 2.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.00  --sup_immed_bw_main                     []
% 2.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.00  
% 2.65/1.00  ------ Combination Options
% 2.65/1.00  
% 2.65/1.00  --comb_res_mult                         3
% 2.65/1.00  --comb_sup_mult                         2
% 2.65/1.00  --comb_inst_mult                        10
% 2.65/1.00  
% 2.65/1.00  ------ Debug Options
% 2.65/1.00  
% 2.65/1.00  --dbg_backtrace                         false
% 2.65/1.00  --dbg_dump_prop_clauses                 false
% 2.65/1.00  --dbg_dump_prop_clauses_file            -
% 2.65/1.00  --dbg_out_stat                          false
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  ------ Proving...
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  % SZS status Theorem for theBenchmark.p
% 2.65/1.00  
% 2.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/1.00  
% 2.65/1.00  fof(f6,conjecture,(
% 2.65/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.00  
% 2.65/1.00  fof(f7,negated_conjecture,(
% 2.65/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.65/1.00    inference(negated_conjecture,[],[f6])).
% 2.65/1.00  
% 2.65/1.00  fof(f16,plain,(
% 2.65/1.00    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.65/1.00    inference(ennf_transformation,[],[f7])).
% 2.65/1.00  
% 2.65/1.00  fof(f17,plain,(
% 2.65/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.65/1.00    inference(flattening,[],[f16])).
% 2.65/1.00  
% 2.65/1.00  fof(f19,plain,(
% 2.65/1.00    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(sK1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 2.65/1.00    introduced(choice_axiom,[])).
% 2.65/1.00  
% 2.65/1.00  fof(f18,plain,(
% 2.65/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.65/1.00    introduced(choice_axiom,[])).
% 2.65/1.00  
% 2.65/1.00  fof(f20,plain,(
% 2.65/1.00    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(sK1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 2.65/1.00  
% 2.65/1.00  fof(f30,plain,(
% 2.65/1.00    v1_funct_1(sK0)),
% 2.65/1.00    inference(cnf_transformation,[],[f20])).
% 2.65/1.00  
% 2.65/1.00  fof(f3,axiom,(
% 2.65/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.00  
% 2.65/1.00  fof(f10,plain,(
% 2.65/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/1.00    inference(ennf_transformation,[],[f3])).
% 2.65/1.00  
% 2.65/1.00  fof(f11,plain,(
% 2.65/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/1.00    inference(flattening,[],[f10])).
% 2.65/1.00  
% 2.65/1.00  fof(f23,plain,(
% 2.65/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/1.00    inference(cnf_transformation,[],[f11])).
% 2.65/1.00  
% 2.65/1.00  fof(f29,plain,(
% 2.65/1.00    v1_relat_1(sK0)),
% 2.65/1.00    inference(cnf_transformation,[],[f20])).
% 2.65/1.00  
% 2.65/1.00  fof(f1,axiom,(
% 2.65/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 2.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.00  
% 2.65/1.00  fof(f8,plain,(
% 2.65/1.00    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.65/1.00    inference(ennf_transformation,[],[f1])).
% 2.65/1.00  
% 2.65/1.00  fof(f21,plain,(
% 2.65/1.00    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.65/1.00    inference(cnf_transformation,[],[f8])).
% 2.65/1.00  
% 2.65/1.00  fof(f5,axiom,(
% 2.65/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.00  
% 2.65/1.00  fof(f14,plain,(
% 2.65/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/1.00    inference(ennf_transformation,[],[f5])).
% 2.65/1.00  
% 2.65/1.00  fof(f15,plain,(
% 2.65/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/1.00    inference(flattening,[],[f14])).
% 2.65/1.00  
% 2.65/1.00  fof(f28,plain,(
% 2.65/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/1.00    inference(cnf_transformation,[],[f15])).
% 2.65/1.00  
% 2.65/1.00  fof(f33,plain,(
% 2.65/1.00    v2_funct_1(sK0)),
% 2.65/1.00    inference(cnf_transformation,[],[f20])).
% 2.65/1.00  
% 2.65/1.00  fof(f34,plain,(
% 2.65/1.00    k1_relat_1(sK1) = k2_relat_1(sK0)),
% 2.65/1.00    inference(cnf_transformation,[],[f20])).
% 2.65/1.00  
% 2.65/1.00  fof(f27,plain,(
% 2.65/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/1.00    inference(cnf_transformation,[],[f15])).
% 2.65/1.00  
% 2.65/1.00  fof(f2,axiom,(
% 2.65/1.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.00  
% 2.65/1.00  fof(f9,plain,(
% 2.65/1.00    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.65/1.00    inference(ennf_transformation,[],[f2])).
% 2.65/1.00  
% 2.65/1.00  fof(f22,plain,(
% 2.65/1.00    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.65/1.00    inference(cnf_transformation,[],[f9])).
% 2.65/1.00  
% 2.65/1.00  fof(f4,axiom,(
% 2.65/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/1.00  
% 2.65/1.00  fof(f12,plain,(
% 2.65/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/1.00    inference(ennf_transformation,[],[f4])).
% 2.65/1.00  
% 2.65/1.00  fof(f13,plain,(
% 2.65/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/1.00    inference(flattening,[],[f12])).
% 2.65/1.00  
% 2.65/1.00  fof(f25,plain,(
% 2.65/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/1.00    inference(cnf_transformation,[],[f13])).
% 2.65/1.00  
% 2.65/1.00  fof(f31,plain,(
% 2.65/1.00    v1_relat_1(sK1)),
% 2.65/1.00    inference(cnf_transformation,[],[f20])).
% 2.65/1.00  
% 2.65/1.00  fof(f35,plain,(
% 2.65/1.00    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 2.65/1.00    inference(cnf_transformation,[],[f20])).
% 2.65/1.00  
% 2.65/1.00  fof(f36,plain,(
% 2.65/1.00    k2_funct_1(sK0) != sK1),
% 2.65/1.00    inference(cnf_transformation,[],[f20])).
% 2.65/1.00  
% 2.65/1.00  cnf(c_14,negated_conjecture,
% 2.65/1.00      ( v1_funct_1(sK0) ),
% 2.65/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_248,negated_conjecture,
% 2.65/1.00      ( v1_funct_1(sK0) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_430,plain,
% 2.65/1.00      ( v1_funct_1(sK0) = iProver_top ),
% 2.65/1.00      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3,plain,
% 2.65/1.00      ( ~ v1_funct_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X0)
% 2.65/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 2.65/1.00      inference(cnf_transformation,[],[f23]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_254,plain,
% 2.65/1.00      ( ~ v1_funct_1(X0_39)
% 2.65/1.00      | ~ v1_relat_1(X0_39)
% 2.65/1.00      | v1_relat_1(k2_funct_1(X0_39)) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_427,plain,
% 2.65/1.00      ( v1_funct_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(k2_funct_1(X0_39)) = iProver_top ),
% 2.65/1.00      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_15,negated_conjecture,
% 2.65/1.00      ( v1_relat_1(sK0) ),
% 2.65/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_247,negated_conjecture,
% 2.65/1.00      ( v1_relat_1(sK0) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_431,plain,
% 2.65/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 2.65/1.00      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_0,plain,
% 2.65/1.00      ( ~ v1_relat_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X1)
% 2.65/1.00      | ~ v1_relat_1(X2)
% 2.65/1.00      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 2.65/1.00      inference(cnf_transformation,[],[f21]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_257,plain,
% 2.65/1.00      ( ~ v1_relat_1(X0_39)
% 2.65/1.00      | ~ v1_relat_1(X1_39)
% 2.65/1.00      | ~ v1_relat_1(X2_39)
% 2.65/1.00      | k5_relat_1(k5_relat_1(X2_39,X1_39),X0_39) = k5_relat_1(X2_39,k5_relat_1(X1_39,X0_39)) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_424,plain,
% 2.65/1.00      ( k5_relat_1(k5_relat_1(X0_39,X1_39),X2_39) = k5_relat_1(X0_39,k5_relat_1(X1_39,X2_39))
% 2.65/1.00      | v1_relat_1(X2_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X1_39) != iProver_top ),
% 2.65/1.00      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_927,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(X0_39),k5_relat_1(X1_39,X2_39)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_39),X1_39),X2_39)
% 2.65/1.00      | v1_funct_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X2_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X1_39) != iProver_top ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_427,c_424]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_1664,plain,
% 2.65/1.00      ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0_39),X1_39) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0_39,X1_39))
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X1_39) != iProver_top
% 2.65/1.00      | v1_relat_1(sK0) != iProver_top ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_430,c_927]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_16,plain,
% 2.65/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 2.65/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3243,plain,
% 2.65/1.00      ( v1_relat_1(X1_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top
% 2.65/1.00      | k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0_39),X1_39) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0_39,X1_39)) ),
% 2.65/1.00      inference(global_propositional_subsumption,
% 2.65/1.00                [status(thm)],
% 2.65/1.00                [c_1664,c_16]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3244,plain,
% 2.65/1.00      ( k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0_39),X1_39) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0_39,X1_39))
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X1_39) != iProver_top ),
% 2.65/1.00      inference(renaming,[status(thm)],[c_3243]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3251,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0_39)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X0_39)
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_431,c_3244]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_6,plain,
% 2.65/1.00      ( ~ v2_funct_1(X0)
% 2.65/1.00      | ~ v1_funct_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X0)
% 2.65/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 2.65/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_11,negated_conjecture,
% 2.65/1.00      ( v2_funct_1(sK0) ),
% 2.65/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_156,plain,
% 2.65/1.00      ( ~ v1_funct_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X0)
% 2.65/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 2.65/1.00      | sK0 != X0 ),
% 2.65/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_157,plain,
% 2.65/1.00      ( ~ v1_funct_1(sK0)
% 2.65/1.00      | ~ v1_relat_1(sK0)
% 2.65/1.00      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.65/1.00      inference(unflattening,[status(thm)],[c_156]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_25,plain,
% 2.65/1.00      ( ~ v2_funct_1(sK0)
% 2.65/1.00      | ~ v1_funct_1(sK0)
% 2.65/1.00      | ~ v1_relat_1(sK0)
% 2.65/1.00      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.65/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_159,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.65/1.00      inference(global_propositional_subsumption,
% 2.65/1.00                [status(thm)],
% 2.65/1.00                [c_157,c_15,c_14,c_11,c_25]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_245,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_159]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_10,negated_conjecture,
% 2.65/1.00      ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
% 2.65/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_251,negated_conjecture,
% 2.65/1.00      ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_453,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
% 2.65/1.00      inference(light_normalisation,[status(thm)],[c_245,c_251]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3263,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0_39)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),X0_39)
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 2.65/1.00      inference(light_normalisation,[status(thm)],[c_3251,c_453]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3284,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,k2_funct_1(X0_39))) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(X0_39))
% 2.65/1.00      | v1_funct_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_427,c_3263]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3837,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(sK0))
% 2.65/1.00      | v1_relat_1(sK0) != iProver_top ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_430,c_3284]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_7,plain,
% 2.65/1.00      ( ~ v2_funct_1(X0)
% 2.65/1.00      | ~ v1_funct_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X0)
% 2.65/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 2.65/1.00      inference(cnf_transformation,[],[f27]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_148,plain,
% 2.65/1.00      ( ~ v1_funct_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X0)
% 2.65/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 2.65/1.00      | sK0 != X0 ),
% 2.65/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_149,plain,
% 2.65/1.00      ( ~ v1_funct_1(sK0)
% 2.65/1.00      | ~ v1_relat_1(sK0)
% 2.65/1.00      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.65/1.00      inference(unflattening,[status(thm)],[c_148]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_22,plain,
% 2.65/1.00      ( ~ v2_funct_1(sK0)
% 2.65/1.00      | ~ v1_funct_1(sK0)
% 2.65/1.00      | ~ v1_relat_1(sK0)
% 2.65/1.00      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.65/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_151,plain,
% 2.65/1.00      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.65/1.00      inference(global_propositional_subsumption,
% 2.65/1.00                [status(thm)],
% 2.65/1.00                [c_149,c_15,c_14,c_11,c_22]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_246,plain,
% 2.65/1.00      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_151]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_1,plain,
% 2.65/1.00      ( ~ v1_relat_1(X0)
% 2.65/1.00      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 2.65/1.00      inference(cnf_transformation,[],[f22]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_256,plain,
% 2.65/1.00      ( ~ v1_relat_1(X0_39)
% 2.65/1.00      | k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39 ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_425,plain,
% 2.65/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(X0_39)),X0_39) = X0_39
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 2.65/1.00      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_774,plain,
% 2.65/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(X0_39))),k2_funct_1(X0_39)) = k2_funct_1(X0_39)
% 2.65/1.00      | v1_funct_1(X0_39) != iProver_top
% 2.65/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_427,c_425]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_838,plain,
% 2.65/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) = k2_funct_1(sK0)
% 2.65/1.00      | v1_relat_1(sK0) != iProver_top ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_430,c_774]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_5,plain,
% 2.65/1.00      ( ~ v2_funct_1(X0)
% 2.65/1.00      | ~ v1_funct_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X0)
% 2.65/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.65/1.00      inference(cnf_transformation,[],[f25]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_164,plain,
% 2.65/1.00      ( ~ v1_funct_1(X0)
% 2.65/1.00      | ~ v1_relat_1(X0)
% 2.65/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.65/1.00      | sK0 != X0 ),
% 2.65/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_165,plain,
% 2.65/1.00      ( ~ v1_funct_1(sK0)
% 2.65/1.00      | ~ v1_relat_1(sK0)
% 2.65/1.00      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.65/1.00      inference(unflattening,[status(thm)],[c_164]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_28,plain,
% 2.65/1.00      ( ~ v2_funct_1(sK0)
% 2.65/1.00      | ~ v1_funct_1(sK0)
% 2.65/1.00      | ~ v1_relat_1(sK0)
% 2.65/1.00      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.65/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_167,plain,
% 2.65/1.00      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.65/1.00      inference(global_propositional_subsumption,
% 2.65/1.00                [status(thm)],
% 2.65/1.00                [c_165,c_15,c_14,c_11,c_28]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_244,plain,
% 2.65/1.00      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_167]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_444,plain,
% 2.65/1.00      ( k1_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK1) ),
% 2.65/1.00      inference(light_normalisation,[status(thm)],[c_244,c_251]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_850,plain,
% 2.65/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(sK0)) = k2_funct_1(sK0)
% 2.65/1.00      | v1_relat_1(sK0) != iProver_top ),
% 2.65/1.00      inference(light_normalisation,[status(thm)],[c_838,c_444]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_863,plain,
% 2.65/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k2_funct_1(sK0)) = k2_funct_1(sK0) ),
% 2.65/1.00      inference(global_propositional_subsumption,
% 2.65/1.00                [status(thm)],
% 2.65/1.00                [c_850,c_16]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_13,negated_conjecture,
% 2.65/1.00      ( v1_relat_1(sK1) ),
% 2.65/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_249,negated_conjecture,
% 2.65/1.00      ( v1_relat_1(sK1) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_429,plain,
% 2.65/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 2.65/1.00      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3282,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_429,c_3263]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_9,negated_conjecture,
% 2.65/1.00      ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.65/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_252,negated_conjecture,
% 2.65/1.00      ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_632,plain,
% 2.65/1.00      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
% 2.65/1.00      inference(superposition,[status(thm)],[c_429,c_425]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3294,plain,
% 2.65/1.00      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = sK1 ),
% 2.65/1.00      inference(light_normalisation,[status(thm)],[c_3282,c_252,c_632]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_3849,plain,
% 2.65/1.00      ( k2_funct_1(sK0) = sK1 | v1_relat_1(sK0) != iProver_top ),
% 2.65/1.00      inference(light_normalisation,
% 2.65/1.00                [status(thm)],
% 2.65/1.00                [c_3837,c_246,c_863,c_3294]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_8,negated_conjecture,
% 2.65/1.00      ( k2_funct_1(sK0) != sK1 ),
% 2.65/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(c_253,negated_conjecture,
% 2.65/1.00      ( k2_funct_1(sK0) != sK1 ),
% 2.65/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.65/1.00  
% 2.65/1.00  cnf(contradiction,plain,
% 2.65/1.00      ( $false ),
% 2.65/1.00      inference(minisat,[status(thm)],[c_3849,c_253,c_16]) ).
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/1.00  
% 2.65/1.00  ------                               Statistics
% 2.65/1.00  
% 2.65/1.00  ------ General
% 2.65/1.00  
% 2.65/1.00  abstr_ref_over_cycles:                  0
% 2.65/1.00  abstr_ref_under_cycles:                 0
% 2.65/1.00  gc_basic_clause_elim:                   0
% 2.65/1.00  forced_gc_time:                         0
% 2.65/1.00  parsing_time:                           0.009
% 2.65/1.00  unif_index_cands_time:                  0.
% 2.65/1.00  unif_index_add_time:                    0.
% 2.65/1.00  orderings_time:                         0.
% 2.65/1.00  out_proof_time:                         0.011
% 2.65/1.00  total_time:                             0.176
% 2.65/1.00  num_of_symbols:                         43
% 2.65/1.00  num_of_terms:                           2985
% 2.65/1.00  
% 2.65/1.00  ------ Preprocessing
% 2.65/1.00  
% 2.65/1.00  num_of_splits:                          0
% 2.65/1.00  num_of_split_atoms:                     0
% 2.65/1.00  num_of_reused_defs:                     0
% 2.65/1.00  num_eq_ax_congr_red:                    0
% 2.65/1.00  num_of_sem_filtered_clauses:            1
% 2.65/1.00  num_of_subtypes:                        2
% 2.65/1.00  monotx_restored_types:                  0
% 2.65/1.00  sat_num_of_epr_types:                   0
% 2.65/1.00  sat_num_of_non_cyclic_types:            0
% 2.65/1.00  sat_guarded_non_collapsed_types:        1
% 2.65/1.00  num_pure_diseq_elim:                    0
% 2.65/1.00  simp_replaced_by:                       0
% 2.65/1.00  res_preprocessed:                       84
% 2.65/1.00  prep_upred:                             0
% 2.65/1.00  prep_unflattend:                        4
% 2.65/1.00  smt_new_axioms:                         0
% 2.65/1.00  pred_elim_cands:                        2
% 2.65/1.00  pred_elim:                              1
% 2.65/1.00  pred_elim_cl:                           1
% 2.65/1.00  pred_elim_cycles:                       3
% 2.65/1.00  merged_defs:                            0
% 2.65/1.00  merged_defs_ncl:                        0
% 2.65/1.00  bin_hyper_res:                          0
% 2.65/1.00  prep_cycles:                            4
% 2.65/1.00  pred_elim_time:                         0.001
% 2.65/1.00  splitting_time:                         0.
% 2.65/1.00  sem_filter_time:                        0.
% 2.65/1.00  monotx_time:                            0.
% 2.65/1.00  subtype_inf_time:                       0.
% 2.65/1.00  
% 2.65/1.00  ------ Problem properties
% 2.65/1.00  
% 2.65/1.00  clauses:                                15
% 2.65/1.00  conjectures:                            7
% 2.65/1.00  epr:                                    4
% 2.65/1.00  horn:                                   15
% 2.65/1.00  ground:                                 11
% 2.65/1.00  unary:                                  11
% 2.65/1.00  binary:                                 1
% 2.65/1.00  lits:                                   23
% 2.65/1.00  lits_eq:                                9
% 2.65/1.00  fd_pure:                                0
% 2.65/1.00  fd_pseudo:                              0
% 2.65/1.00  fd_cond:                                0
% 2.65/1.00  fd_pseudo_cond:                         0
% 2.65/1.00  ac_symbols:                             0
% 2.65/1.00  
% 2.65/1.00  ------ Propositional Solver
% 2.65/1.00  
% 2.65/1.00  prop_solver_calls:                      34
% 2.65/1.00  prop_fast_solver_calls:                 512
% 2.65/1.00  smt_solver_calls:                       0
% 2.65/1.00  smt_fast_solver_calls:                  0
% 2.65/1.00  prop_num_of_clauses:                    1393
% 2.65/1.00  prop_preprocess_simplified:             3198
% 2.65/1.00  prop_fo_subsumed:                       29
% 2.65/1.00  prop_solver_time:                       0.
% 2.65/1.00  smt_solver_time:                        0.
% 2.65/1.00  smt_fast_solver_time:                   0.
% 2.65/1.00  prop_fast_solver_time:                  0.
% 2.65/1.00  prop_unsat_core_time:                   0.
% 2.65/1.00  
% 2.65/1.00  ------ QBF
% 2.65/1.00  
% 2.65/1.00  qbf_q_res:                              0
% 2.65/1.00  qbf_num_tautologies:                    0
% 2.65/1.00  qbf_prep_cycles:                        0
% 2.65/1.00  
% 2.65/1.00  ------ BMC1
% 2.65/1.00  
% 2.65/1.00  bmc1_current_bound:                     -1
% 2.65/1.00  bmc1_last_solved_bound:                 -1
% 2.65/1.00  bmc1_unsat_core_size:                   -1
% 2.65/1.00  bmc1_unsat_core_parents_size:           -1
% 2.65/1.00  bmc1_merge_next_fun:                    0
% 2.65/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.65/1.00  
% 2.65/1.00  ------ Instantiation
% 2.65/1.00  
% 2.65/1.00  inst_num_of_clauses:                    745
% 2.65/1.00  inst_num_in_passive:                    113
% 2.65/1.00  inst_num_in_active:                     361
% 2.65/1.00  inst_num_in_unprocessed:                271
% 2.65/1.00  inst_num_of_loops:                      390
% 2.65/1.00  inst_num_of_learning_restarts:          0
% 2.65/1.00  inst_num_moves_active_passive:          18
% 2.65/1.00  inst_lit_activity:                      0
% 2.65/1.00  inst_lit_activity_moves:                0
% 2.65/1.00  inst_num_tautologies:                   0
% 2.65/1.00  inst_num_prop_implied:                  0
% 2.65/1.00  inst_num_existing_simplified:           0
% 2.65/1.00  inst_num_eq_res_simplified:             0
% 2.65/1.00  inst_num_child_elim:                    0
% 2.65/1.00  inst_num_of_dismatching_blockings:      193
% 2.65/1.00  inst_num_of_non_proper_insts:           814
% 2.65/1.00  inst_num_of_duplicates:                 0
% 2.65/1.00  inst_inst_num_from_inst_to_res:         0
% 2.65/1.00  inst_dismatching_checking_time:         0.
% 2.65/1.00  
% 2.65/1.00  ------ Resolution
% 2.65/1.00  
% 2.65/1.00  res_num_of_clauses:                     0
% 2.65/1.00  res_num_in_passive:                     0
% 2.65/1.00  res_num_in_active:                      0
% 2.65/1.00  res_num_of_loops:                       88
% 2.65/1.00  res_forward_subset_subsumed:            170
% 2.65/1.00  res_backward_subset_subsumed:           0
% 2.65/1.00  res_forward_subsumed:                   0
% 2.65/1.00  res_backward_subsumed:                  0
% 2.65/1.00  res_forward_subsumption_resolution:     0
% 2.65/1.00  res_backward_subsumption_resolution:    0
% 2.65/1.00  res_clause_to_clause_subsumption:       317
% 2.65/1.00  res_orphan_elimination:                 0
% 2.65/1.00  res_tautology_del:                      135
% 2.65/1.00  res_num_eq_res_simplified:              0
% 2.65/1.00  res_num_sel_changes:                    0
% 2.65/1.00  res_moves_from_active_to_pass:          0
% 2.65/1.00  
% 2.65/1.00  ------ Superposition
% 2.65/1.00  
% 2.65/1.00  sup_time_total:                         0.
% 2.65/1.00  sup_time_generating:                    0.
% 2.65/1.00  sup_time_sim_full:                      0.
% 2.65/1.00  sup_time_sim_immed:                     0.
% 2.65/1.00  
% 2.65/1.00  sup_num_of_clauses:                     99
% 2.65/1.00  sup_num_in_active:                      78
% 2.65/1.00  sup_num_in_passive:                     21
% 2.65/1.00  sup_num_of_loops:                       77
% 2.65/1.00  sup_fw_superposition:                   83
% 2.65/1.00  sup_bw_superposition:                   1
% 2.65/1.00  sup_immediate_simplified:               13
% 2.65/1.00  sup_given_eliminated:                   0
% 2.65/1.00  comparisons_done:                       0
% 2.65/1.00  comparisons_avoided:                    0
% 2.65/1.00  
% 2.65/1.00  ------ Simplifications
% 2.65/1.00  
% 2.65/1.00  
% 2.65/1.00  sim_fw_subset_subsumed:                 0
% 2.65/1.00  sim_bw_subset_subsumed:                 0
% 2.65/1.00  sim_fw_subsumed:                        0
% 2.65/1.00  sim_bw_subsumed:                        0
% 2.65/1.00  sim_fw_subsumption_res:                 0
% 2.65/1.00  sim_bw_subsumption_res:                 0
% 2.65/1.00  sim_tautology_del:                      0
% 2.65/1.00  sim_eq_tautology_del:                   0
% 2.65/1.00  sim_eq_res_simp:                        0
% 2.65/1.00  sim_fw_demodulated:                     0
% 2.65/1.00  sim_bw_demodulated:                     0
% 2.65/1.00  sim_light_normalised:                   15
% 2.65/1.00  sim_joinable_taut:                      0
% 2.65/1.00  sim_joinable_simp:                      0
% 2.65/1.00  sim_ac_normalised:                      0
% 2.65/1.00  sim_smt_subsumption:                    0
% 2.65/1.00  
%------------------------------------------------------------------------------
