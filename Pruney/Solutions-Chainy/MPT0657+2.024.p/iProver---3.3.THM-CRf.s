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
% DateTime   : Thu Dec  3 11:50:53 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 397 expanded)
%              Number of clauses        :   71 ( 119 expanded)
%              Number of leaves         :   10 ( 100 expanded)
%              Depth                    :   18
%              Number of atoms          :  419 (2581 expanded)
%              Number of equality atoms :  227 (1059 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(sK1,X0) = k6_relat_1(k2_relat_1(X0))
        & k2_relat_1(sK1) = k1_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
            & k2_relat_1(X1) = k1_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(X1,sK0) = k6_relat_1(k2_relat_1(sK0))
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))
    & k2_relat_1(sK1) = k1_relat_1(sK0)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_147,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_431,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_155,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_funct_1(X0_38)
    | ~ v2_funct_1(X0_38)
    | k5_relat_1(X0_38,k2_funct_1(X0_38)) = k6_relat_1(k1_relat_1(X0_38)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_426,plain,
    ( k5_relat_1(X0_38,k2_funct_1(X0_38)) = k6_relat_1(k1_relat_1(X0_38))
    | v1_relat_1(X0_38) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v2_funct_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_1107,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_426])).

cnf(c_10,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_152,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1124,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1107,c_152])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_204,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_176,plain,
    ( k6_relat_1(X0_39) = k6_relat_1(X1_39)
    | X0_39 != X1_39 ),
    theory(equality)).

cnf(c_584,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k6_relat_1(X0_39)
    | k2_relat_1(sK1) != X0_39 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_617,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k6_relat_1(k1_relat_1(sK0))
    | k2_relat_1(sK1) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_169,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_574,plain,
    ( k5_relat_1(X0_38,k2_funct_1(sK0)) != X0_40
    | k5_relat_1(X0_38,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
    | k6_relat_1(k2_relat_1(sK1)) != X0_40 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_583,plain,
    ( k5_relat_1(X0_38,k2_funct_1(sK0)) != k6_relat_1(X0_39)
    | k5_relat_1(X0_38,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
    | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(X0_39) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_632,plain,
    ( k5_relat_1(X0_38,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k5_relat_1(X0_38,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
    | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_633,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
    | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1291,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1124,c_15,c_14,c_11,c_204,c_152,c_617,c_633])).

cnf(c_9,negated_conjecture,
    ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_153,negated_conjecture,
    ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | X0 = X2
    | k5_relat_1(X2,X1) != k6_relat_1(k1_relat_1(X0))
    | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_159,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | ~ v1_relat_1(X2_38)
    | ~ v1_funct_1(X0_38)
    | ~ v1_funct_1(X1_38)
    | ~ v1_funct_1(X2_38)
    | k5_relat_1(X2_38,X1_38) != k6_relat_1(k1_relat_1(X0_38))
    | k5_relat_1(X1_38,X0_38) != k6_relat_1(k2_relat_1(X2_38))
    | X0_38 = X2_38 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_422,plain,
    ( k5_relat_1(X0_38,X1_38) != k6_relat_1(k1_relat_1(X2_38))
    | k5_relat_1(X1_38,X2_38) != k6_relat_1(k2_relat_1(X0_38))
    | X2_38 = X0_38
    | v1_relat_1(X2_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top
    | v1_funct_1(X2_38) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v1_funct_1(X1_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_1149,plain,
    ( k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
    | k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
    | sK1 = X0_38
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_153,c_422])).

cnf(c_16,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20,plain,
    ( v2_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_36,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_38,plain,
    ( v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_39,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_41,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) = iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_8,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_154,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_167,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_556,plain,
    ( k2_funct_1(sK0) != X0_38
    | k2_funct_1(sK0) = sK1
    | sK1 != X0_38 ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_156,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_funct_1(X0_38)
    | ~ v2_funct_1(X0_38)
    | k5_relat_1(k2_funct_1(X0_38),X0_38) = k6_relat_1(k2_relat_1(X0_38)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_425,plain,
    ( k5_relat_1(k2_funct_1(X0_38),X0_38) = k6_relat_1(k2_relat_1(X0_38))
    | v1_relat_1(X0_38) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v2_funct_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_969,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_425])).

cnf(c_201,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_1049,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_969,c_15,c_14,c_11,c_201])).

cnf(c_1150,plain,
    ( k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
    | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,X0_38)
    | k2_funct_1(sK0) = X0_38
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_422])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_158,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_funct_1(X0_38)
    | ~ v2_funct_1(X0_38)
    | k2_relat_1(k2_funct_1(X0_38)) = k1_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_423,plain,
    ( k2_relat_1(k2_funct_1(X0_38)) = k1_relat_1(X0_38)
    | v1_relat_1(X0_38) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v2_funct_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_727,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_423])).

cnf(c_744,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK1)
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_727,c_152])).

cnf(c_805,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_17,c_20])).

cnf(c_1179,plain,
    ( k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
    | k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
    | k2_funct_1(sK0) = X0_38
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1150,c_805])).

cnf(c_1297,plain,
    ( k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
    | k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
    | v1_relat_1(X0_38) != iProver_top
    | v1_funct_1(X0_38) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1149,c_16,c_17,c_18,c_19,c_20,c_38,c_41,c_154,c_556,c_1179])).

cnf(c_1298,plain,
    ( k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
    | k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
    | v1_relat_1(X0_38) != iProver_top
    | v1_funct_1(X0_38) != iProver_top ),
    inference(renaming,[status(thm)],[c_1297])).

cnf(c_1307,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK0))) != k6_relat_1(k2_relat_1(sK0))
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1298])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_157,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_funct_1(X0_38)
    | ~ v2_funct_1(X0_38)
    | k1_relat_1(k2_funct_1(X0_38)) = k2_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_424,plain,
    ( k1_relat_1(k2_funct_1(X0_38)) = k2_relat_1(X0_38)
    | v1_relat_1(X0_38) != iProver_top
    | v1_funct_1(X0_38) != iProver_top
    | v2_funct_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_871,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_424])).

cnf(c_198,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_960,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_15,c_14,c_11,c_198])).

cnf(c_1308,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1307,c_960])).

cnf(c_1309,plain,
    ( v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1308])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1309,c_41,c_38,c_20,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:32:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.95/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.95/1.00  
% 0.95/1.00  ------  iProver source info
% 0.95/1.00  
% 0.95/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.95/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.95/1.00  git: non_committed_changes: false
% 0.95/1.00  git: last_make_outside_of_git: false
% 0.95/1.00  
% 0.95/1.00  ------ 
% 0.95/1.00  
% 0.95/1.00  ------ Input Options
% 0.95/1.00  
% 0.95/1.00  --out_options                           all
% 0.95/1.00  --tptp_safe_out                         true
% 0.95/1.00  --problem_path                          ""
% 0.95/1.00  --include_path                          ""
% 0.95/1.00  --clausifier                            res/vclausify_rel
% 0.95/1.00  --clausifier_options                    --mode clausify
% 0.95/1.00  --stdin                                 false
% 0.95/1.00  --stats_out                             all
% 0.95/1.00  
% 0.95/1.00  ------ General Options
% 0.95/1.00  
% 0.95/1.00  --fof                                   false
% 0.95/1.00  --time_out_real                         305.
% 0.95/1.00  --time_out_virtual                      -1.
% 0.95/1.00  --symbol_type_check                     false
% 0.95/1.00  --clausify_out                          false
% 0.95/1.00  --sig_cnt_out                           false
% 0.95/1.00  --trig_cnt_out                          false
% 0.95/1.00  --trig_cnt_out_tolerance                1.
% 0.95/1.00  --trig_cnt_out_sk_spl                   false
% 0.95/1.00  --abstr_cl_out                          false
% 0.95/1.00  
% 0.95/1.00  ------ Global Options
% 0.95/1.00  
% 0.95/1.00  --schedule                              default
% 0.95/1.00  --add_important_lit                     false
% 0.95/1.00  --prop_solver_per_cl                    1000
% 0.95/1.00  --min_unsat_core                        false
% 0.95/1.00  --soft_assumptions                      false
% 0.95/1.00  --soft_lemma_size                       3
% 0.95/1.00  --prop_impl_unit_size                   0
% 0.95/1.00  --prop_impl_unit                        []
% 0.95/1.00  --share_sel_clauses                     true
% 0.95/1.00  --reset_solvers                         false
% 0.95/1.00  --bc_imp_inh                            [conj_cone]
% 0.95/1.00  --conj_cone_tolerance                   3.
% 0.95/1.00  --extra_neg_conj                        none
% 0.95/1.00  --large_theory_mode                     true
% 0.95/1.00  --prolific_symb_bound                   200
% 0.95/1.00  --lt_threshold                          2000
% 0.95/1.00  --clause_weak_htbl                      true
% 0.95/1.00  --gc_record_bc_elim                     false
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing Options
% 0.95/1.00  
% 0.95/1.00  --preprocessing_flag                    true
% 0.95/1.00  --time_out_prep_mult                    0.1
% 0.95/1.00  --splitting_mode                        input
% 0.95/1.00  --splitting_grd                         true
% 0.95/1.00  --splitting_cvd                         false
% 0.95/1.00  --splitting_cvd_svl                     false
% 0.95/1.00  --splitting_nvd                         32
% 0.95/1.00  --sub_typing                            true
% 0.95/1.00  --prep_gs_sim                           true
% 0.95/1.00  --prep_unflatten                        true
% 0.95/1.00  --prep_res_sim                          true
% 0.95/1.00  --prep_upred                            true
% 0.95/1.00  --prep_sem_filter                       exhaustive
% 0.95/1.00  --prep_sem_filter_out                   false
% 0.95/1.00  --pred_elim                             true
% 0.95/1.00  --res_sim_input                         true
% 0.95/1.00  --eq_ax_congr_red                       true
% 0.95/1.00  --pure_diseq_elim                       true
% 0.95/1.00  --brand_transform                       false
% 0.95/1.00  --non_eq_to_eq                          false
% 0.95/1.00  --prep_def_merge                        true
% 0.95/1.00  --prep_def_merge_prop_impl              false
% 0.95/1.00  --prep_def_merge_mbd                    true
% 0.95/1.00  --prep_def_merge_tr_red                 false
% 0.95/1.00  --prep_def_merge_tr_cl                  false
% 0.95/1.00  --smt_preprocessing                     true
% 0.95/1.00  --smt_ac_axioms                         fast
% 0.95/1.00  --preprocessed_out                      false
% 0.95/1.00  --preprocessed_stats                    false
% 0.95/1.00  
% 0.95/1.00  ------ Abstraction refinement Options
% 0.95/1.00  
% 0.95/1.00  --abstr_ref                             []
% 0.95/1.00  --abstr_ref_prep                        false
% 0.95/1.00  --abstr_ref_until_sat                   false
% 0.95/1.00  --abstr_ref_sig_restrict                funpre
% 0.95/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/1.00  --abstr_ref_under                       []
% 0.95/1.00  
% 0.95/1.00  ------ SAT Options
% 0.95/1.00  
% 0.95/1.00  --sat_mode                              false
% 0.95/1.00  --sat_fm_restart_options                ""
% 0.95/1.00  --sat_gr_def                            false
% 0.95/1.00  --sat_epr_types                         true
% 0.95/1.00  --sat_non_cyclic_types                  false
% 0.95/1.00  --sat_finite_models                     false
% 0.95/1.00  --sat_fm_lemmas                         false
% 0.95/1.00  --sat_fm_prep                           false
% 0.95/1.00  --sat_fm_uc_incr                        true
% 0.95/1.00  --sat_out_model                         small
% 0.95/1.00  --sat_out_clauses                       false
% 0.95/1.00  
% 0.95/1.00  ------ QBF Options
% 0.95/1.00  
% 0.95/1.00  --qbf_mode                              false
% 0.95/1.00  --qbf_elim_univ                         false
% 0.95/1.00  --qbf_dom_inst                          none
% 0.95/1.00  --qbf_dom_pre_inst                      false
% 0.95/1.00  --qbf_sk_in                             false
% 0.95/1.00  --qbf_pred_elim                         true
% 0.95/1.00  --qbf_split                             512
% 0.95/1.00  
% 0.95/1.00  ------ BMC1 Options
% 0.95/1.00  
% 0.95/1.00  --bmc1_incremental                      false
% 0.95/1.00  --bmc1_axioms                           reachable_all
% 0.95/1.00  --bmc1_min_bound                        0
% 0.95/1.00  --bmc1_max_bound                        -1
% 0.95/1.00  --bmc1_max_bound_default                -1
% 0.95/1.00  --bmc1_symbol_reachability              true
% 0.95/1.00  --bmc1_property_lemmas                  false
% 0.95/1.00  --bmc1_k_induction                      false
% 0.95/1.00  --bmc1_non_equiv_states                 false
% 0.95/1.00  --bmc1_deadlock                         false
% 0.95/1.00  --bmc1_ucm                              false
% 0.95/1.00  --bmc1_add_unsat_core                   none
% 0.95/1.00  --bmc1_unsat_core_children              false
% 0.95/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/1.00  --bmc1_out_stat                         full
% 0.95/1.00  --bmc1_ground_init                      false
% 0.95/1.00  --bmc1_pre_inst_next_state              false
% 0.95/1.00  --bmc1_pre_inst_state                   false
% 0.95/1.00  --bmc1_pre_inst_reach_state             false
% 0.95/1.00  --bmc1_out_unsat_core                   false
% 0.95/1.00  --bmc1_aig_witness_out                  false
% 0.95/1.00  --bmc1_verbose                          false
% 0.95/1.00  --bmc1_dump_clauses_tptp                false
% 0.95/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.95/1.00  --bmc1_dump_file                        -
% 0.95/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.95/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.95/1.00  --bmc1_ucm_extend_mode                  1
% 0.95/1.00  --bmc1_ucm_init_mode                    2
% 0.95/1.00  --bmc1_ucm_cone_mode                    none
% 0.95/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.95/1.00  --bmc1_ucm_relax_model                  4
% 0.95/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.95/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/1.00  --bmc1_ucm_layered_model                none
% 0.95/1.00  --bmc1_ucm_max_lemma_size               10
% 0.95/1.00  
% 0.95/1.00  ------ AIG Options
% 0.95/1.00  
% 0.95/1.00  --aig_mode                              false
% 0.95/1.00  
% 0.95/1.00  ------ Instantiation Options
% 0.95/1.00  
% 0.95/1.00  --instantiation_flag                    true
% 0.95/1.00  --inst_sos_flag                         false
% 0.95/1.00  --inst_sos_phase                        true
% 0.95/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/1.00  --inst_lit_sel_side                     num_symb
% 0.95/1.00  --inst_solver_per_active                1400
% 0.95/1.00  --inst_solver_calls_frac                1.
% 0.95/1.00  --inst_passive_queue_type               priority_queues
% 0.95/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/1.00  --inst_passive_queues_freq              [25;2]
% 0.95/1.00  --inst_dismatching                      true
% 0.95/1.00  --inst_eager_unprocessed_to_passive     true
% 0.95/1.00  --inst_prop_sim_given                   true
% 0.95/1.00  --inst_prop_sim_new                     false
% 0.95/1.00  --inst_subs_new                         false
% 0.95/1.00  --inst_eq_res_simp                      false
% 0.95/1.00  --inst_subs_given                       false
% 0.95/1.00  --inst_orphan_elimination               true
% 0.95/1.00  --inst_learning_loop_flag               true
% 0.95/1.00  --inst_learning_start                   3000
% 0.95/1.00  --inst_learning_factor                  2
% 0.95/1.00  --inst_start_prop_sim_after_learn       3
% 0.95/1.00  --inst_sel_renew                        solver
% 0.95/1.00  --inst_lit_activity_flag                true
% 0.95/1.00  --inst_restr_to_given                   false
% 0.95/1.00  --inst_activity_threshold               500
% 0.95/1.00  --inst_out_proof                        true
% 0.95/1.00  
% 0.95/1.00  ------ Resolution Options
% 0.95/1.00  
% 0.95/1.00  --resolution_flag                       true
% 0.95/1.00  --res_lit_sel                           adaptive
% 0.95/1.00  --res_lit_sel_side                      none
% 0.95/1.00  --res_ordering                          kbo
% 0.95/1.00  --res_to_prop_solver                    active
% 0.95/1.00  --res_prop_simpl_new                    false
% 0.95/1.00  --res_prop_simpl_given                  true
% 0.95/1.00  --res_passive_queue_type                priority_queues
% 0.95/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/1.00  --res_passive_queues_freq               [15;5]
% 0.95/1.00  --res_forward_subs                      full
% 0.95/1.00  --res_backward_subs                     full
% 0.95/1.00  --res_forward_subs_resolution           true
% 0.95/1.00  --res_backward_subs_resolution          true
% 0.95/1.00  --res_orphan_elimination                true
% 0.95/1.00  --res_time_limit                        2.
% 0.95/1.00  --res_out_proof                         true
% 0.95/1.00  
% 0.95/1.00  ------ Superposition Options
% 0.95/1.00  
% 0.95/1.00  --superposition_flag                    true
% 0.95/1.00  --sup_passive_queue_type                priority_queues
% 0.95/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.95/1.00  --demod_completeness_check              fast
% 0.95/1.00  --demod_use_ground                      true
% 0.95/1.00  --sup_to_prop_solver                    passive
% 0.95/1.00  --sup_prop_simpl_new                    true
% 0.95/1.00  --sup_prop_simpl_given                  true
% 0.95/1.00  --sup_fun_splitting                     false
% 0.95/1.00  --sup_smt_interval                      50000
% 0.95/1.00  
% 0.95/1.00  ------ Superposition Simplification Setup
% 0.95/1.00  
% 0.95/1.00  --sup_indices_passive                   []
% 0.95/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_full_bw                           [BwDemod]
% 0.95/1.00  --sup_immed_triv                        [TrivRules]
% 0.95/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_immed_bw_main                     []
% 0.95/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.00  
% 0.95/1.00  ------ Combination Options
% 0.95/1.00  
% 0.95/1.00  --comb_res_mult                         3
% 0.95/1.00  --comb_sup_mult                         2
% 0.95/1.00  --comb_inst_mult                        10
% 0.95/1.00  
% 0.95/1.00  ------ Debug Options
% 0.95/1.00  
% 0.95/1.00  --dbg_backtrace                         false
% 0.95/1.00  --dbg_dump_prop_clauses                 false
% 0.95/1.00  --dbg_dump_prop_clauses_file            -
% 0.95/1.00  --dbg_out_stat                          false
% 0.95/1.00  ------ Parsing...
% 0.95/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.95/1.00  ------ Proving...
% 0.95/1.00  ------ Problem Properties 
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  clauses                                 16
% 0.95/1.00  conjectures                             8
% 0.95/1.00  EPR                                     5
% 0.95/1.00  Horn                                    16
% 0.95/1.00  unary                                   8
% 0.95/1.00  binary                                  0
% 0.95/1.00  lits                                    45
% 0.95/1.00  lits eq                                 10
% 0.95/1.00  fd_pure                                 0
% 0.95/1.00  fd_pseudo                               0
% 0.95/1.00  fd_cond                                 0
% 0.95/1.00  fd_pseudo_cond                          1
% 0.95/1.00  AC symbols                              0
% 0.95/1.00  
% 0.95/1.00  ------ Schedule dynamic 5 is on 
% 0.95/1.00  
% 0.95/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  ------ 
% 0.95/1.00  Current options:
% 0.95/1.00  ------ 
% 0.95/1.00  
% 0.95/1.00  ------ Input Options
% 0.95/1.00  
% 0.95/1.00  --out_options                           all
% 0.95/1.00  --tptp_safe_out                         true
% 0.95/1.00  --problem_path                          ""
% 0.95/1.00  --include_path                          ""
% 0.95/1.00  --clausifier                            res/vclausify_rel
% 0.95/1.00  --clausifier_options                    --mode clausify
% 0.95/1.00  --stdin                                 false
% 0.95/1.00  --stats_out                             all
% 0.95/1.00  
% 0.95/1.00  ------ General Options
% 0.95/1.00  
% 0.95/1.00  --fof                                   false
% 0.95/1.00  --time_out_real                         305.
% 0.95/1.00  --time_out_virtual                      -1.
% 0.95/1.00  --symbol_type_check                     false
% 0.95/1.00  --clausify_out                          false
% 0.95/1.00  --sig_cnt_out                           false
% 0.95/1.00  --trig_cnt_out                          false
% 0.95/1.00  --trig_cnt_out_tolerance                1.
% 0.95/1.00  --trig_cnt_out_sk_spl                   false
% 0.95/1.00  --abstr_cl_out                          false
% 0.95/1.00  
% 0.95/1.00  ------ Global Options
% 0.95/1.00  
% 0.95/1.00  --schedule                              default
% 0.95/1.00  --add_important_lit                     false
% 0.95/1.00  --prop_solver_per_cl                    1000
% 0.95/1.00  --min_unsat_core                        false
% 0.95/1.00  --soft_assumptions                      false
% 0.95/1.00  --soft_lemma_size                       3
% 0.95/1.00  --prop_impl_unit_size                   0
% 0.95/1.00  --prop_impl_unit                        []
% 0.95/1.00  --share_sel_clauses                     true
% 0.95/1.00  --reset_solvers                         false
% 0.95/1.00  --bc_imp_inh                            [conj_cone]
% 0.95/1.00  --conj_cone_tolerance                   3.
% 0.95/1.00  --extra_neg_conj                        none
% 0.95/1.00  --large_theory_mode                     true
% 0.95/1.00  --prolific_symb_bound                   200
% 0.95/1.00  --lt_threshold                          2000
% 0.95/1.00  --clause_weak_htbl                      true
% 0.95/1.00  --gc_record_bc_elim                     false
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing Options
% 0.95/1.00  
% 0.95/1.00  --preprocessing_flag                    true
% 0.95/1.00  --time_out_prep_mult                    0.1
% 0.95/1.00  --splitting_mode                        input
% 0.95/1.00  --splitting_grd                         true
% 0.95/1.00  --splitting_cvd                         false
% 0.95/1.00  --splitting_cvd_svl                     false
% 0.95/1.00  --splitting_nvd                         32
% 0.95/1.00  --sub_typing                            true
% 0.95/1.00  --prep_gs_sim                           true
% 0.95/1.00  --prep_unflatten                        true
% 0.95/1.00  --prep_res_sim                          true
% 0.95/1.00  --prep_upred                            true
% 0.95/1.00  --prep_sem_filter                       exhaustive
% 0.95/1.00  --prep_sem_filter_out                   false
% 0.95/1.00  --pred_elim                             true
% 0.95/1.00  --res_sim_input                         true
% 0.95/1.00  --eq_ax_congr_red                       true
% 0.95/1.00  --pure_diseq_elim                       true
% 0.95/1.00  --brand_transform                       false
% 0.95/1.00  --non_eq_to_eq                          false
% 0.95/1.00  --prep_def_merge                        true
% 0.95/1.00  --prep_def_merge_prop_impl              false
% 0.95/1.00  --prep_def_merge_mbd                    true
% 0.95/1.00  --prep_def_merge_tr_red                 false
% 0.95/1.00  --prep_def_merge_tr_cl                  false
% 0.95/1.00  --smt_preprocessing                     true
% 0.95/1.00  --smt_ac_axioms                         fast
% 0.95/1.00  --preprocessed_out                      false
% 0.95/1.00  --preprocessed_stats                    false
% 0.95/1.00  
% 0.95/1.00  ------ Abstraction refinement Options
% 0.95/1.00  
% 0.95/1.00  --abstr_ref                             []
% 0.95/1.00  --abstr_ref_prep                        false
% 0.95/1.00  --abstr_ref_until_sat                   false
% 0.95/1.00  --abstr_ref_sig_restrict                funpre
% 0.95/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/1.00  --abstr_ref_under                       []
% 0.95/1.00  
% 0.95/1.00  ------ SAT Options
% 0.95/1.00  
% 0.95/1.00  --sat_mode                              false
% 0.95/1.00  --sat_fm_restart_options                ""
% 0.95/1.00  --sat_gr_def                            false
% 0.95/1.00  --sat_epr_types                         true
% 0.95/1.00  --sat_non_cyclic_types                  false
% 0.95/1.00  --sat_finite_models                     false
% 0.95/1.00  --sat_fm_lemmas                         false
% 0.95/1.00  --sat_fm_prep                           false
% 0.95/1.00  --sat_fm_uc_incr                        true
% 0.95/1.00  --sat_out_model                         small
% 0.95/1.00  --sat_out_clauses                       false
% 0.95/1.00  
% 0.95/1.00  ------ QBF Options
% 0.95/1.00  
% 0.95/1.00  --qbf_mode                              false
% 0.95/1.00  --qbf_elim_univ                         false
% 0.95/1.00  --qbf_dom_inst                          none
% 0.95/1.00  --qbf_dom_pre_inst                      false
% 0.95/1.00  --qbf_sk_in                             false
% 0.95/1.00  --qbf_pred_elim                         true
% 0.95/1.00  --qbf_split                             512
% 0.95/1.00  
% 0.95/1.00  ------ BMC1 Options
% 0.95/1.00  
% 0.95/1.00  --bmc1_incremental                      false
% 0.95/1.00  --bmc1_axioms                           reachable_all
% 0.95/1.00  --bmc1_min_bound                        0
% 0.95/1.00  --bmc1_max_bound                        -1
% 0.95/1.00  --bmc1_max_bound_default                -1
% 0.95/1.00  --bmc1_symbol_reachability              true
% 0.95/1.00  --bmc1_property_lemmas                  false
% 0.95/1.00  --bmc1_k_induction                      false
% 0.95/1.00  --bmc1_non_equiv_states                 false
% 0.95/1.00  --bmc1_deadlock                         false
% 0.95/1.00  --bmc1_ucm                              false
% 0.95/1.00  --bmc1_add_unsat_core                   none
% 0.95/1.00  --bmc1_unsat_core_children              false
% 0.95/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/1.00  --bmc1_out_stat                         full
% 0.95/1.00  --bmc1_ground_init                      false
% 0.95/1.00  --bmc1_pre_inst_next_state              false
% 0.95/1.00  --bmc1_pre_inst_state                   false
% 0.95/1.00  --bmc1_pre_inst_reach_state             false
% 0.95/1.00  --bmc1_out_unsat_core                   false
% 0.95/1.00  --bmc1_aig_witness_out                  false
% 0.95/1.00  --bmc1_verbose                          false
% 0.95/1.00  --bmc1_dump_clauses_tptp                false
% 0.95/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.95/1.00  --bmc1_dump_file                        -
% 0.95/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.95/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.95/1.00  --bmc1_ucm_extend_mode                  1
% 0.95/1.00  --bmc1_ucm_init_mode                    2
% 0.95/1.00  --bmc1_ucm_cone_mode                    none
% 0.95/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.95/1.00  --bmc1_ucm_relax_model                  4
% 0.95/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.95/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/1.00  --bmc1_ucm_layered_model                none
% 0.95/1.00  --bmc1_ucm_max_lemma_size               10
% 0.95/1.00  
% 0.95/1.00  ------ AIG Options
% 0.95/1.00  
% 0.95/1.00  --aig_mode                              false
% 0.95/1.00  
% 0.95/1.00  ------ Instantiation Options
% 0.95/1.00  
% 0.95/1.00  --instantiation_flag                    true
% 0.95/1.00  --inst_sos_flag                         false
% 0.95/1.00  --inst_sos_phase                        true
% 0.95/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/1.00  --inst_lit_sel_side                     none
% 0.95/1.00  --inst_solver_per_active                1400
% 0.95/1.00  --inst_solver_calls_frac                1.
% 0.95/1.00  --inst_passive_queue_type               priority_queues
% 0.95/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/1.00  --inst_passive_queues_freq              [25;2]
% 0.95/1.00  --inst_dismatching                      true
% 0.95/1.00  --inst_eager_unprocessed_to_passive     true
% 0.95/1.00  --inst_prop_sim_given                   true
% 0.95/1.00  --inst_prop_sim_new                     false
% 0.95/1.00  --inst_subs_new                         false
% 0.95/1.00  --inst_eq_res_simp                      false
% 0.95/1.00  --inst_subs_given                       false
% 0.95/1.00  --inst_orphan_elimination               true
% 0.95/1.00  --inst_learning_loop_flag               true
% 0.95/1.00  --inst_learning_start                   3000
% 0.95/1.00  --inst_learning_factor                  2
% 0.95/1.00  --inst_start_prop_sim_after_learn       3
% 0.95/1.00  --inst_sel_renew                        solver
% 0.95/1.00  --inst_lit_activity_flag                true
% 0.95/1.00  --inst_restr_to_given                   false
% 0.95/1.00  --inst_activity_threshold               500
% 0.95/1.00  --inst_out_proof                        true
% 0.95/1.00  
% 0.95/1.00  ------ Resolution Options
% 0.95/1.00  
% 0.95/1.00  --resolution_flag                       false
% 0.95/1.00  --res_lit_sel                           adaptive
% 0.95/1.00  --res_lit_sel_side                      none
% 0.95/1.00  --res_ordering                          kbo
% 0.95/1.00  --res_to_prop_solver                    active
% 0.95/1.00  --res_prop_simpl_new                    false
% 0.95/1.00  --res_prop_simpl_given                  true
% 0.95/1.00  --res_passive_queue_type                priority_queues
% 0.95/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/1.00  --res_passive_queues_freq               [15;5]
% 0.95/1.00  --res_forward_subs                      full
% 0.95/1.00  --res_backward_subs                     full
% 0.95/1.00  --res_forward_subs_resolution           true
% 0.95/1.00  --res_backward_subs_resolution          true
% 0.95/1.00  --res_orphan_elimination                true
% 0.95/1.00  --res_time_limit                        2.
% 0.95/1.00  --res_out_proof                         true
% 0.95/1.00  
% 0.95/1.00  ------ Superposition Options
% 0.95/1.00  
% 0.95/1.00  --superposition_flag                    true
% 0.95/1.00  --sup_passive_queue_type                priority_queues
% 0.95/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.95/1.00  --demod_completeness_check              fast
% 0.95/1.00  --demod_use_ground                      true
% 0.95/1.00  --sup_to_prop_solver                    passive
% 0.95/1.00  --sup_prop_simpl_new                    true
% 0.95/1.00  --sup_prop_simpl_given                  true
% 0.95/1.00  --sup_fun_splitting                     false
% 0.95/1.00  --sup_smt_interval                      50000
% 0.95/1.00  
% 0.95/1.00  ------ Superposition Simplification Setup
% 0.95/1.00  
% 0.95/1.00  --sup_indices_passive                   []
% 0.95/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_full_bw                           [BwDemod]
% 0.95/1.00  --sup_immed_triv                        [TrivRules]
% 0.95/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_immed_bw_main                     []
% 0.95/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.00  
% 0.95/1.00  ------ Combination Options
% 0.95/1.00  
% 0.95/1.00  --comb_res_mult                         3
% 0.95/1.00  --comb_sup_mult                         2
% 0.95/1.00  --comb_inst_mult                        10
% 0.95/1.00  
% 0.95/1.00  ------ Debug Options
% 0.95/1.00  
% 0.95/1.00  --dbg_backtrace                         false
% 0.95/1.00  --dbg_dump_prop_clauses                 false
% 0.95/1.00  --dbg_dump_prop_clauses_file            -
% 0.95/1.00  --dbg_out_stat                          false
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  ------ Proving...
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  % SZS status Theorem for theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  fof(f5,conjecture,(
% 0.95/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f6,negated_conjecture,(
% 0.95/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.95/1.00    inference(negated_conjecture,[],[f5])).
% 0.95/1.00  
% 0.95/1.00  fof(f15,plain,(
% 0.95/1.00    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.95/1.00    inference(ennf_transformation,[],[f6])).
% 0.95/1.00  
% 0.95/1.00  fof(f16,plain,(
% 0.95/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.95/1.00    inference(flattening,[],[f15])).
% 0.95/1.00  
% 0.95/1.00  fof(f18,plain,(
% 0.95/1.00    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(sK1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(sK1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 0.95/1.00    introduced(choice_axiom,[])).
% 0.95/1.00  
% 0.95/1.00  fof(f17,plain,(
% 0.95/1.00    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(X1,sK0) = k6_relat_1(k2_relat_1(sK0)) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.95/1.00    introduced(choice_axiom,[])).
% 0.95/1.00  
% 0.95/1.00  fof(f19,plain,(
% 0.95/1.00    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) & k2_relat_1(sK1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).
% 0.95/1.00  
% 0.95/1.00  fof(f28,plain,(
% 0.95/1.00    v1_relat_1(sK0)),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f4,axiom,(
% 0.95/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f13,plain,(
% 0.95/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.95/1.00    inference(ennf_transformation,[],[f4])).
% 0.95/1.00  
% 0.95/1.00  fof(f14,plain,(
% 0.95/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.95/1.00    inference(flattening,[],[f13])).
% 0.95/1.00  
% 0.95/1.00  fof(f26,plain,(
% 0.95/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f14])).
% 0.95/1.00  
% 0.95/1.00  fof(f33,plain,(
% 0.95/1.00    k2_relat_1(sK1) = k1_relat_1(sK0)),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f29,plain,(
% 0.95/1.00    v1_funct_1(sK0)),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f32,plain,(
% 0.95/1.00    v2_funct_1(sK0)),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f34,plain,(
% 0.95/1.00    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f2,axiom,(
% 0.95/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f9,plain,(
% 0.95/1.00    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.95/1.00    inference(ennf_transformation,[],[f2])).
% 0.95/1.00  
% 0.95/1.00  fof(f10,plain,(
% 0.95/1.00    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.95/1.00    inference(flattening,[],[f9])).
% 0.95/1.00  
% 0.95/1.00  fof(f23,plain,(
% 0.95/1.00    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f10])).
% 0.95/1.00  
% 0.95/1.00  fof(f36,plain,(
% 0.95/1.00    ( ! [X2,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.95/1.00    inference(equality_resolution,[],[f23])).
% 0.95/1.00  
% 0.95/1.00  fof(f30,plain,(
% 0.95/1.00    v1_relat_1(sK1)),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f31,plain,(
% 0.95/1.00    v1_funct_1(sK1)),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f1,axiom,(
% 0.95/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f7,plain,(
% 0.95/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.95/1.00    inference(ennf_transformation,[],[f1])).
% 0.95/1.00  
% 0.95/1.00  fof(f8,plain,(
% 0.95/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.95/1.00    inference(flattening,[],[f7])).
% 0.95/1.00  
% 0.95/1.00  fof(f20,plain,(
% 0.95/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f8])).
% 0.95/1.00  
% 0.95/1.00  fof(f21,plain,(
% 0.95/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f8])).
% 0.95/1.00  
% 0.95/1.00  fof(f35,plain,(
% 0.95/1.00    k2_funct_1(sK0) != sK1),
% 0.95/1.00    inference(cnf_transformation,[],[f19])).
% 0.95/1.00  
% 0.95/1.00  fof(f27,plain,(
% 0.95/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f14])).
% 0.95/1.00  
% 0.95/1.00  fof(f3,axiom,(
% 0.95/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f11,plain,(
% 0.95/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.95/1.00    inference(ennf_transformation,[],[f3])).
% 0.95/1.00  
% 0.95/1.00  fof(f12,plain,(
% 0.95/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.95/1.00    inference(flattening,[],[f11])).
% 0.95/1.00  
% 0.95/1.00  fof(f25,plain,(
% 0.95/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f12])).
% 0.95/1.00  
% 0.95/1.00  fof(f24,plain,(
% 0.95/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f12])).
% 0.95/1.00  
% 0.95/1.00  cnf(c_15,negated_conjecture,
% 0.95/1.00      ( v1_relat_1(sK0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f28]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_147,negated_conjecture,
% 0.95/1.00      ( v1_relat_1(sK0) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_431,plain,
% 0.95/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_147]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_7,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0)
% 0.95/1.00      | ~ v1_funct_1(X0)
% 0.95/1.00      | ~ v2_funct_1(X0)
% 0.95/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 0.95/1.00      inference(cnf_transformation,[],[f26]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_155,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0_38)
% 0.95/1.00      | ~ v1_funct_1(X0_38)
% 0.95/1.00      | ~ v2_funct_1(X0_38)
% 0.95/1.00      | k5_relat_1(X0_38,k2_funct_1(X0_38)) = k6_relat_1(k1_relat_1(X0_38)) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_426,plain,
% 0.95/1.00      ( k5_relat_1(X0_38,k2_funct_1(X0_38)) = k6_relat_1(k1_relat_1(X0_38))
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v2_funct_1(X0_38) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1107,plain,
% 0.95/1.00      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_431,c_426]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_10,negated_conjecture,
% 0.95/1.00      ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f33]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_152,negated_conjecture,
% 0.95/1.00      ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1124,plain,
% 0.95/1.00      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(light_normalisation,[status(thm)],[c_1107,c_152]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_14,negated_conjecture,
% 0.95/1.00      ( v1_funct_1(sK0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f29]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_11,negated_conjecture,
% 0.95/1.00      ( v2_funct_1(sK0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_204,plain,
% 0.95/1.00      ( ~ v1_relat_1(sK0)
% 0.95/1.00      | ~ v1_funct_1(sK0)
% 0.95/1.00      | ~ v2_funct_1(sK0)
% 0.95/1.00      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_155]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_176,plain,
% 0.95/1.00      ( k6_relat_1(X0_39) = k6_relat_1(X1_39) | X0_39 != X1_39 ),
% 0.95/1.00      theory(equality) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_584,plain,
% 0.95/1.00      ( k6_relat_1(k2_relat_1(sK1)) = k6_relat_1(X0_39)
% 0.95/1.00      | k2_relat_1(sK1) != X0_39 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_176]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_617,plain,
% 0.95/1.00      ( k6_relat_1(k2_relat_1(sK1)) = k6_relat_1(k1_relat_1(sK0))
% 0.95/1.00      | k2_relat_1(sK1) != k1_relat_1(sK0) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_584]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_169,plain,
% 0.95/1.00      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 0.95/1.00      theory(equality) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_574,plain,
% 0.95/1.00      ( k5_relat_1(X0_38,k2_funct_1(sK0)) != X0_40
% 0.95/1.00      | k5_relat_1(X0_38,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | k6_relat_1(k2_relat_1(sK1)) != X0_40 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_169]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_583,plain,
% 0.95/1.00      ( k5_relat_1(X0_38,k2_funct_1(sK0)) != k6_relat_1(X0_39)
% 0.95/1.00      | k5_relat_1(X0_38,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(X0_39) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_574]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_632,plain,
% 0.95/1.00      ( k5_relat_1(X0_38,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
% 0.95/1.00      | k5_relat_1(X0_38,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK0)) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_583]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_633,plain,
% 0.95/1.00      ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
% 0.95/1.00      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | k6_relat_1(k2_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK0)) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_632]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1291,plain,
% 0.95/1.00      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k2_relat_1(sK1)) ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_1124,c_15,c_14,c_11,c_204,c_152,c_617,c_633]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_9,negated_conjecture,
% 0.95/1.00      ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 0.95/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_153,negated_conjecture,
% 0.95/1.00      ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_3,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0)
% 0.95/1.00      | ~ v1_relat_1(X1)
% 0.95/1.00      | ~ v1_relat_1(X2)
% 0.95/1.00      | ~ v1_funct_1(X0)
% 0.95/1.00      | ~ v1_funct_1(X1)
% 0.95/1.00      | ~ v1_funct_1(X2)
% 0.95/1.00      | X0 = X2
% 0.95/1.00      | k5_relat_1(X2,X1) != k6_relat_1(k1_relat_1(X0))
% 0.95/1.00      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X2)) ),
% 0.95/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_159,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0_38)
% 0.95/1.00      | ~ v1_relat_1(X1_38)
% 0.95/1.00      | ~ v1_relat_1(X2_38)
% 0.95/1.00      | ~ v1_funct_1(X0_38)
% 0.95/1.00      | ~ v1_funct_1(X1_38)
% 0.95/1.00      | ~ v1_funct_1(X2_38)
% 0.95/1.00      | k5_relat_1(X2_38,X1_38) != k6_relat_1(k1_relat_1(X0_38))
% 0.95/1.00      | k5_relat_1(X1_38,X0_38) != k6_relat_1(k2_relat_1(X2_38))
% 0.95/1.00      | X0_38 = X2_38 ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_422,plain,
% 0.95/1.00      ( k5_relat_1(X0_38,X1_38) != k6_relat_1(k1_relat_1(X2_38))
% 0.95/1.00      | k5_relat_1(X1_38,X2_38) != k6_relat_1(k2_relat_1(X0_38))
% 0.95/1.00      | X2_38 = X0_38
% 0.95/1.00      | v1_relat_1(X2_38) != iProver_top
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_relat_1(X1_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X2_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X1_38) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1149,plain,
% 0.95/1.00      ( k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | sK1 = X0_38
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_relat_1(sK1) != iProver_top
% 0.95/1.00      | v1_relat_1(sK0) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(sK1) != iProver_top
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_153,c_422]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_16,plain,
% 0.95/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_17,plain,
% 0.95/1.00      ( v1_funct_1(sK0) = iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_13,negated_conjecture,
% 0.95/1.00      ( v1_relat_1(sK1) ),
% 0.95/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_18,plain,
% 0.95/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_12,negated_conjecture,
% 0.95/1.00      ( v1_funct_1(sK1) ),
% 0.95/1.00      inference(cnf_transformation,[],[f31]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_19,plain,
% 0.95/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_20,plain,
% 0.95/1.00      ( v2_funct_1(sK0) = iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_2,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0)
% 0.95/1.00      | v1_relat_1(k2_funct_1(X0))
% 0.95/1.00      | ~ v1_funct_1(X0)
% 0.95/1.00      | ~ v2_funct_1(X0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f20]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_36,plain,
% 0.95/1.00      ( v1_relat_1(X0) != iProver_top
% 0.95/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 0.95/1.00      | v1_funct_1(X0) != iProver_top
% 0.95/1.00      | v2_funct_1(X0) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_38,plain,
% 0.95/1.00      ( v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 0.95/1.00      | v1_relat_1(sK0) != iProver_top
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0)
% 0.95/1.00      | ~ v1_funct_1(X0)
% 0.95/1.00      | v1_funct_1(k2_funct_1(X0))
% 0.95/1.00      | ~ v2_funct_1(X0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f21]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_39,plain,
% 0.95/1.00      ( v1_relat_1(X0) != iProver_top
% 0.95/1.00      | v1_funct_1(X0) != iProver_top
% 0.95/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 0.95/1.00      | v2_funct_1(X0) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_41,plain,
% 0.95/1.00      ( v1_relat_1(sK0) != iProver_top
% 0.95/1.00      | v1_funct_1(k2_funct_1(sK0)) = iProver_top
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_39]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_8,negated_conjecture,
% 0.95/1.00      ( k2_funct_1(sK0) != sK1 ),
% 0.95/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_154,negated_conjecture,
% 0.95/1.00      ( k2_funct_1(sK0) != sK1 ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_167,plain,
% 0.95/1.00      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 0.95/1.00      theory(equality) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_556,plain,
% 0.95/1.00      ( k2_funct_1(sK0) != X0_38 | k2_funct_1(sK0) = sK1 | sK1 != X0_38 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_167]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_6,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0)
% 0.95/1.00      | ~ v1_funct_1(X0)
% 0.95/1.00      | ~ v2_funct_1(X0)
% 0.95/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 0.95/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_156,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0_38)
% 0.95/1.00      | ~ v1_funct_1(X0_38)
% 0.95/1.00      | ~ v2_funct_1(X0_38)
% 0.95/1.00      | k5_relat_1(k2_funct_1(X0_38),X0_38) = k6_relat_1(k2_relat_1(X0_38)) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_425,plain,
% 0.95/1.00      ( k5_relat_1(k2_funct_1(X0_38),X0_38) = k6_relat_1(k2_relat_1(X0_38))
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v2_funct_1(X0_38) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_969,plain,
% 0.95/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_431,c_425]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_201,plain,
% 0.95/1.00      ( ~ v1_relat_1(sK0)
% 0.95/1.00      | ~ v1_funct_1(sK0)
% 0.95/1.00      | ~ v2_funct_1(sK0)
% 0.95/1.00      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_156]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1049,plain,
% 0.95/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_969,c_15,c_14,c_11,c_201]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1150,plain,
% 0.95/1.00      ( k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,X0_38)
% 0.95/1.00      | k2_funct_1(sK0) = X0_38
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.95/1.00      | v1_relat_1(sK0) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_1049,c_422]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_4,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0)
% 0.95/1.00      | ~ v1_funct_1(X0)
% 0.95/1.00      | ~ v2_funct_1(X0)
% 0.95/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f25]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_158,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0_38)
% 0.95/1.00      | ~ v1_funct_1(X0_38)
% 0.95/1.00      | ~ v2_funct_1(X0_38)
% 0.95/1.00      | k2_relat_1(k2_funct_1(X0_38)) = k1_relat_1(X0_38) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_423,plain,
% 0.95/1.00      ( k2_relat_1(k2_funct_1(X0_38)) = k1_relat_1(X0_38)
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v2_funct_1(X0_38) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_727,plain,
% 0.95/1.00      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_431,c_423]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_744,plain,
% 0.95/1.00      ( k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK1)
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(light_normalisation,[status(thm)],[c_727,c_152]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_805,plain,
% 0.95/1.00      ( k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK1) ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_744,c_17,c_20]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1179,plain,
% 0.95/1.00      ( k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | k2_funct_1(sK0) = X0_38
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.95/1.00      | v1_relat_1(sK0) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(light_normalisation,[status(thm)],[c_1150,c_805]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1297,plain,
% 0.95/1.00      ( k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_1149,c_16,c_17,c_18,c_19,c_20,c_38,c_41,c_154,c_556,
% 0.95/1.00                 c_1179]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1298,plain,
% 0.95/1.00      ( k5_relat_1(sK0,X0_38) != k6_relat_1(k2_relat_1(sK1))
% 0.95/1.00      | k6_relat_1(k1_relat_1(X0_38)) != k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top ),
% 0.95/1.00      inference(renaming,[status(thm)],[c_1297]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1307,plain,
% 0.95/1.00      ( k6_relat_1(k1_relat_1(k2_funct_1(sK0))) != k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.95/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_1291,c_1298]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_5,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0)
% 0.95/1.00      | ~ v1_funct_1(X0)
% 0.95/1.00      | ~ v2_funct_1(X0)
% 0.95/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f24]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_157,plain,
% 0.95/1.00      ( ~ v1_relat_1(X0_38)
% 0.95/1.00      | ~ v1_funct_1(X0_38)
% 0.95/1.00      | ~ v2_funct_1(X0_38)
% 0.95/1.00      | k1_relat_1(k2_funct_1(X0_38)) = k2_relat_1(X0_38) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_424,plain,
% 0.95/1.00      ( k1_relat_1(k2_funct_1(X0_38)) = k2_relat_1(X0_38)
% 0.95/1.00      | v1_relat_1(X0_38) != iProver_top
% 0.95/1.00      | v1_funct_1(X0_38) != iProver_top
% 0.95/1.00      | v2_funct_1(X0_38) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_871,plain,
% 0.95/1.00      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
% 0.95/1.00      | v1_funct_1(sK0) != iProver_top
% 0.95/1.00      | v2_funct_1(sK0) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_431,c_424]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_198,plain,
% 0.95/1.00      ( ~ v1_relat_1(sK0)
% 0.95/1.00      | ~ v1_funct_1(sK0)
% 0.95/1.00      | ~ v2_funct_1(sK0)
% 0.95/1.00      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_157]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_960,plain,
% 0.95/1.00      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_871,c_15,c_14,c_11,c_198]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1308,plain,
% 0.95/1.00      ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
% 0.95/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.95/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top ),
% 0.95/1.00      inference(light_normalisation,[status(thm)],[c_1307,c_960]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1309,plain,
% 0.95/1.00      ( v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.95/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top ),
% 0.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_1308]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(contradiction,plain,
% 0.95/1.00      ( $false ),
% 0.95/1.00      inference(minisat,[status(thm)],[c_1309,c_41,c_38,c_20,c_17,c_16]) ).
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  ------                               Statistics
% 0.95/1.00  
% 0.95/1.00  ------ General
% 0.95/1.00  
% 0.95/1.00  abstr_ref_over_cycles:                  0
% 0.95/1.00  abstr_ref_under_cycles:                 0
% 0.95/1.00  gc_basic_clause_elim:                   0
% 0.95/1.00  forced_gc_time:                         0
% 0.95/1.00  parsing_time:                           0.008
% 0.95/1.00  unif_index_cands_time:                  0.
% 0.95/1.00  unif_index_add_time:                    0.
% 0.95/1.00  orderings_time:                         0.
% 0.95/1.00  out_proof_time:                         0.014
% 0.95/1.00  total_time:                             0.08
% 0.95/1.00  num_of_symbols:                         41
% 0.95/1.00  num_of_terms:                           882
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing
% 0.95/1.00  
% 0.95/1.00  num_of_splits:                          0
% 0.95/1.00  num_of_split_atoms:                     0
% 0.95/1.00  num_of_reused_defs:                     0
% 0.95/1.00  num_eq_ax_congr_red:                    0
% 0.95/1.00  num_of_sem_filtered_clauses:            1
% 0.95/1.00  num_of_subtypes:                        3
% 0.95/1.00  monotx_restored_types:                  0
% 0.95/1.00  sat_num_of_epr_types:                   0
% 0.95/1.00  sat_num_of_non_cyclic_types:            0
% 0.95/1.00  sat_guarded_non_collapsed_types:        1
% 0.95/1.00  num_pure_diseq_elim:                    0
% 0.95/1.00  simp_replaced_by:                       0
% 0.95/1.00  res_preprocessed:                       77
% 0.95/1.00  prep_upred:                             0
% 0.95/1.00  prep_unflattend:                        0
% 0.95/1.00  smt_new_axioms:                         0
% 0.95/1.00  pred_elim_cands:                        3
% 0.95/1.00  pred_elim:                              0
% 0.95/1.00  pred_elim_cl:                           0
% 0.95/1.00  pred_elim_cycles:                       1
% 0.95/1.00  merged_defs:                            0
% 0.95/1.00  merged_defs_ncl:                        0
% 0.95/1.00  bin_hyper_res:                          0
% 0.95/1.00  prep_cycles:                            3
% 0.95/1.00  pred_elim_time:                         0.
% 0.95/1.00  splitting_time:                         0.
% 0.95/1.00  sem_filter_time:                        0.
% 0.95/1.00  monotx_time:                            0.
% 0.95/1.00  subtype_inf_time:                       0.
% 0.95/1.00  
% 0.95/1.00  ------ Problem properties
% 0.95/1.00  
% 0.95/1.00  clauses:                                16
% 0.95/1.00  conjectures:                            8
% 0.95/1.00  epr:                                    5
% 0.95/1.00  horn:                                   16
% 0.95/1.00  ground:                                 8
% 0.95/1.00  unary:                                  8
% 0.95/1.00  binary:                                 0
% 0.95/1.00  lits:                                   45
% 0.95/1.00  lits_eq:                                10
% 0.95/1.00  fd_pure:                                0
% 0.95/1.00  fd_pseudo:                              0
% 0.95/1.00  fd_cond:                                0
% 0.95/1.00  fd_pseudo_cond:                         1
% 0.95/1.00  ac_symbols:                             0
% 0.95/1.00  
% 0.95/1.00  ------ Propositional Solver
% 0.95/1.00  
% 0.95/1.00  prop_solver_calls:                      24
% 0.95/1.00  prop_fast_solver_calls:                 489
% 0.95/1.00  smt_solver_calls:                       0
% 0.95/1.00  smt_fast_solver_calls:                  0
% 0.95/1.00  prop_num_of_clauses:                    369
% 0.95/1.00  prop_preprocess_simplified:             1925
% 0.95/1.00  prop_fo_subsumed:                       16
% 0.95/1.00  prop_solver_time:                       0.
% 0.95/1.00  smt_solver_time:                        0.
% 0.95/1.00  smt_fast_solver_time:                   0.
% 0.95/1.00  prop_fast_solver_time:                  0.
% 0.95/1.00  prop_unsat_core_time:                   0.
% 0.95/1.00  
% 0.95/1.00  ------ QBF
% 0.95/1.00  
% 0.95/1.00  qbf_q_res:                              0
% 0.95/1.00  qbf_num_tautologies:                    0
% 0.95/1.00  qbf_prep_cycles:                        0
% 0.95/1.00  
% 0.95/1.00  ------ BMC1
% 0.95/1.00  
% 0.95/1.00  bmc1_current_bound:                     -1
% 0.95/1.00  bmc1_last_solved_bound:                 -1
% 0.95/1.00  bmc1_unsat_core_size:                   -1
% 0.95/1.00  bmc1_unsat_core_parents_size:           -1
% 0.95/1.00  bmc1_merge_next_fun:                    0
% 0.95/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.95/1.00  
% 0.95/1.00  ------ Instantiation
% 0.95/1.00  
% 0.95/1.00  inst_num_of_clauses:                    169
% 0.95/1.00  inst_num_in_passive:                    17
% 0.95/1.00  inst_num_in_active:                     109
% 0.95/1.00  inst_num_in_unprocessed:                44
% 0.95/1.00  inst_num_of_loops:                      120
% 0.95/1.00  inst_num_of_learning_restarts:          0
% 0.95/1.00  inst_num_moves_active_passive:          5
% 0.95/1.00  inst_lit_activity:                      0
% 0.95/1.00  inst_lit_activity_moves:                0
% 0.95/1.00  inst_num_tautologies:                   0
% 0.95/1.00  inst_num_prop_implied:                  0
% 0.95/1.00  inst_num_existing_simplified:           0
% 0.95/1.00  inst_num_eq_res_simplified:             0
% 0.95/1.00  inst_num_child_elim:                    0
% 0.95/1.00  inst_num_of_dismatching_blockings:      39
% 0.95/1.00  inst_num_of_non_proper_insts:           149
% 0.95/1.00  inst_num_of_duplicates:                 0
% 0.95/1.00  inst_inst_num_from_inst_to_res:         0
% 0.95/1.00  inst_dismatching_checking_time:         0.
% 0.95/1.00  
% 0.95/1.00  ------ Resolution
% 0.95/1.00  
% 0.95/1.00  res_num_of_clauses:                     0
% 0.95/1.00  res_num_in_passive:                     0
% 0.95/1.00  res_num_in_active:                      0
% 0.95/1.00  res_num_of_loops:                       80
% 0.95/1.00  res_forward_subset_subsumed:            43
% 0.95/1.00  res_backward_subset_subsumed:           4
% 0.95/1.00  res_forward_subsumed:                   0
% 0.95/1.00  res_backward_subsumed:                  0
% 0.95/1.00  res_forward_subsumption_resolution:     0
% 0.95/1.00  res_backward_subsumption_resolution:    0
% 0.95/1.00  res_clause_to_clause_subsumption:       61
% 0.95/1.00  res_orphan_elimination:                 0
% 0.95/1.00  res_tautology_del:                      27
% 0.95/1.00  res_num_eq_res_simplified:              0
% 0.95/1.00  res_num_sel_changes:                    0
% 0.95/1.00  res_moves_from_active_to_pass:          0
% 0.95/1.00  
% 0.95/1.00  ------ Superposition
% 0.95/1.00  
% 0.95/1.00  sup_time_total:                         0.
% 0.95/1.00  sup_time_generating:                    0.
% 0.95/1.00  sup_time_sim_full:                      0.
% 0.95/1.00  sup_time_sim_immed:                     0.
% 0.95/1.00  
% 0.95/1.00  sup_num_of_clauses:                     33
% 0.95/1.00  sup_num_in_active:                      24
% 0.95/1.00  sup_num_in_passive:                     9
% 0.95/1.00  sup_num_of_loops:                       23
% 0.95/1.00  sup_fw_superposition:                   16
% 0.95/1.00  sup_bw_superposition:                   1
% 0.95/1.00  sup_immediate_simplified:               4
% 0.95/1.00  sup_given_eliminated:                   0
% 0.95/1.00  comparisons_done:                       0
% 0.95/1.00  comparisons_avoided:                    0
% 0.95/1.00  
% 0.95/1.00  ------ Simplifications
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  sim_fw_subset_subsumed:                 0
% 0.95/1.00  sim_bw_subset_subsumed:                 0
% 0.95/1.00  sim_fw_subsumed:                        0
% 0.95/1.00  sim_bw_subsumed:                        0
% 0.95/1.00  sim_fw_subsumption_res:                 0
% 0.95/1.00  sim_bw_subsumption_res:                 0
% 0.95/1.00  sim_tautology_del:                      0
% 0.95/1.00  sim_eq_tautology_del:                   0
% 0.95/1.00  sim_eq_res_simp:                        1
% 0.95/1.00  sim_fw_demodulated:                     0
% 0.95/1.00  sim_bw_demodulated:                     0
% 0.95/1.00  sim_light_normalised:                   4
% 0.95/1.00  sim_joinable_taut:                      0
% 0.95/1.00  sim_joinable_simp:                      0
% 0.95/1.00  sim_ac_normalised:                      0
% 0.95/1.00  sim_smt_subsumption:                    0
% 0.95/1.00  
%------------------------------------------------------------------------------
