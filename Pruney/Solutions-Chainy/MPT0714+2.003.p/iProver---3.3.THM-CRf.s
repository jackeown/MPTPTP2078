%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:52 EST 2020

% Result     : Theorem 14.96s
% Output     : CNFRefutation 14.96s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 342 expanded)
%              Number of clauses        :   63 ( 131 expanded)
%              Number of leaves         :   11 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          :  220 (1168 expanded)
%              Number of equality atoms :  109 ( 365 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
     => k5_relat_1(k7_relat_1(X0,sK2),k7_relat_1(X1,k9_relat_1(X0,sK2))) != k7_relat_1(k5_relat_1(X0,X1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(sK1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,sK1),X2)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_150,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_428,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_154,plain,
    ( ~ v1_funct_1(X0_38)
    | ~ v1_relat_1(X0_38)
    | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_425,plain,
    ( v1_funct_1(X0_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(k7_relat_1(X0_38,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_159,plain,
    ( ~ v1_relat_1(X0_38)
    | k5_relat_1(X0_38,k6_relat_1(k2_relat_1(X0_38))) = X0_38 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_420,plain,
    ( k5_relat_1(X0_38,k6_relat_1(k2_relat_1(X0_38))) = X0_38
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_829,plain,
    ( k5_relat_1(k7_relat_1(X0_38,X0_39),k6_relat_1(k2_relat_1(k7_relat_1(X0_38,X0_39)))) = k7_relat_1(X0_38,X0_39)
    | v1_funct_1(X0_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_425,c_420])).

cnf(c_6799,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(k2_relat_1(k7_relat_1(sK0,X0_39)))) = k7_relat_1(sK0,X0_39)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_428,c_829])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_149,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_429,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_161,plain,
    ( ~ v1_relat_1(X0_38)
    | k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_418,plain,
    ( k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_687,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0_39)) = k9_relat_1(sK0,X0_39) ),
    inference(superposition,[status(thm)],[c_429,c_418])).

cnf(c_6817,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(k9_relat_1(sK0,X0_39))) = k7_relat_1(sK0,X0_39)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6799,c_687])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_156,plain,
    ( v1_relat_1(k6_relat_1(X0_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_423,plain,
    ( v1_relat_1(k6_relat_1(X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k7_relat_1(X1,X2),X0) = k7_relat_1(k5_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_162,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | k5_relat_1(k7_relat_1(X1_38,X0_39),X0_38) = k7_relat_1(k5_relat_1(X1_38,X0_38),X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_417,plain,
    ( k5_relat_1(k7_relat_1(X0_38,X0_39),X1_38) = k7_relat_1(k5_relat_1(X0_38,X1_38),X0_39)
    | v1_relat_1(X1_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_662,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),X0_38) = k7_relat_1(k5_relat_1(sK0,X0_38),X0_39)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_429,c_417])).

cnf(c_1528,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(X1_39)) = k7_relat_1(k5_relat_1(sK0,k6_relat_1(X1_39)),X0_39) ),
    inference(superposition,[status(thm)],[c_423,c_662])).

cnf(c_6818,plain,
    ( k7_relat_1(k5_relat_1(sK0,k6_relat_1(k9_relat_1(sK0,X0_39))),X0_39) = k7_relat_1(sK0,X0_39)
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6817,c_1528])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_39363,plain,
    ( k7_relat_1(k5_relat_1(sK0,k6_relat_1(k9_relat_1(sK0,X0_39))),X0_39) = k7_relat_1(sK0,X0_39) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6818,c_14])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_151,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_427,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_160,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | ~ v1_relat_1(X2_38)
    | k5_relat_1(k5_relat_1(X2_38,X1_38),X0_38) = k5_relat_1(X2_38,k5_relat_1(X1_38,X0_38)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_419,plain,
    ( k5_relat_1(k5_relat_1(X0_38,X1_38),X2_38) = k5_relat_1(X0_38,k5_relat_1(X1_38,X2_38))
    | v1_relat_1(X2_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_1217,plain,
    ( k5_relat_1(k7_relat_1(X0_38,X0_39),k5_relat_1(X1_38,X2_38)) = k5_relat_1(k5_relat_1(k7_relat_1(X0_38,X0_39),X1_38),X2_38)
    | v1_funct_1(X0_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top
    | v1_relat_1(X2_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_425,c_419])).

cnf(c_8138,plain,
    ( k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),X0_38),X1_38) = k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(X0_38,X1_38))
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_428,c_1217])).

cnf(c_8768,plain,
    ( v1_relat_1(X1_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top
    | k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),X0_38),X1_38) = k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(X0_38,X1_38)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8138,c_14])).

cnf(c_8769,plain,
    ( k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),X0_38),X1_38) = k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(X0_38,X1_38))
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top ),
    inference(renaming,[status(thm)],[c_8768])).

cnf(c_8778,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(k6_relat_1(X1_39),X0_38)) = k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(X1_39)),X0_38)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_423,c_8769])).

cnf(c_8781,plain,
    ( k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X0_39)),X1_39),X0_38) = k5_relat_1(k7_relat_1(sK0,X1_39),k5_relat_1(k6_relat_1(X0_39),X0_38))
    | v1_relat_1(X0_38) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8778,c_1528])).

cnf(c_66260,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(k6_relat_1(X1_39),sK1)) = k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X1_39)),X0_39),sK1) ),
    inference(superposition,[status(thm)],[c_427,c_8781])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_158,plain,
    ( ~ v1_relat_1(X0_38)
    | k5_relat_1(k6_relat_1(X0_39),X0_38) = k7_relat_1(X0_38,X0_39) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_421,plain,
    ( k5_relat_1(k6_relat_1(X0_39),X0_38) = k7_relat_1(X0_38,X0_39)
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_758,plain,
    ( k5_relat_1(k6_relat_1(X0_39),sK1) = k7_relat_1(sK1,X0_39) ),
    inference(superposition,[status(thm)],[c_427,c_421])).

cnf(c_10,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_152,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_426,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_1527,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k7_relat_1(X0_38,X1_39)) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(X0_38,X1_39)),X0_39)
    | v1_funct_1(X0_38) != iProver_top
    | v1_relat_1(X0_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_425,c_662])).

cnf(c_4910,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k7_relat_1(sK1,X1_39)) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X1_39)),X0_39)
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_1527])).

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5224,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),k7_relat_1(sK1,X1_39)) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X1_39)),X0_39) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4910,c_16])).

cnf(c_66281,plain,
    ( k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X0_39)),X1_39),sK1) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X0_39)),X1_39) ),
    inference(demodulation,[status(thm)],[c_66260,c_758,c_5224])).

cnf(c_68497,plain,
    ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0_39))),X0_39) = k5_relat_1(k7_relat_1(sK0,X0_39),sK1) ),
    inference(superposition,[status(thm)],[c_39363,c_66281])).

cnf(c_1525,plain,
    ( k5_relat_1(k7_relat_1(sK0,X0_39),sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X0_39) ),
    inference(superposition,[status(thm)],[c_427,c_662])).

cnf(c_68506,plain,
    ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0_39))),X0_39) = k7_relat_1(k5_relat_1(sK0,sK1),X0_39) ),
    inference(light_normalisation,[status(thm)],[c_68497,c_1525])).

cnf(c_68509,plain,
    ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,sK2))),sK2) = k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_68506])).

cnf(c_9,negated_conjecture,
    ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_153,negated_conjecture,
    ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5228,plain,
    ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,sK2))),sK2) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_5224,c_153])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_68509,c_5228])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 14.96/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.96/2.49  
% 14.96/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.96/2.49  
% 14.96/2.49  ------  iProver source info
% 14.96/2.49  
% 14.96/2.49  git: date: 2020-06-30 10:37:57 +0100
% 14.96/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.96/2.49  git: non_committed_changes: false
% 14.96/2.49  git: last_make_outside_of_git: false
% 14.96/2.49  
% 14.96/2.49  ------ 
% 14.96/2.49  
% 14.96/2.49  ------ Input Options
% 14.96/2.49  
% 14.96/2.49  --out_options                           all
% 14.96/2.49  --tptp_safe_out                         true
% 14.96/2.49  --problem_path                          ""
% 14.96/2.49  --include_path                          ""
% 14.96/2.49  --clausifier                            res/vclausify_rel
% 14.96/2.49  --clausifier_options                    --mode clausify
% 14.96/2.49  --stdin                                 false
% 14.96/2.49  --stats_out                             all
% 14.96/2.49  
% 14.96/2.49  ------ General Options
% 14.96/2.49  
% 14.96/2.49  --fof                                   false
% 14.96/2.49  --time_out_real                         305.
% 14.96/2.49  --time_out_virtual                      -1.
% 14.96/2.49  --symbol_type_check                     false
% 14.96/2.49  --clausify_out                          false
% 14.96/2.49  --sig_cnt_out                           false
% 14.96/2.49  --trig_cnt_out                          false
% 14.96/2.49  --trig_cnt_out_tolerance                1.
% 14.96/2.49  --trig_cnt_out_sk_spl                   false
% 14.96/2.49  --abstr_cl_out                          false
% 14.96/2.49  
% 14.96/2.49  ------ Global Options
% 14.96/2.49  
% 14.96/2.49  --schedule                              default
% 14.96/2.49  --add_important_lit                     false
% 14.96/2.49  --prop_solver_per_cl                    1000
% 14.96/2.49  --min_unsat_core                        false
% 14.96/2.49  --soft_assumptions                      false
% 14.96/2.49  --soft_lemma_size                       3
% 14.96/2.49  --prop_impl_unit_size                   0
% 14.96/2.49  --prop_impl_unit                        []
% 14.96/2.49  --share_sel_clauses                     true
% 14.96/2.49  --reset_solvers                         false
% 14.96/2.49  --bc_imp_inh                            [conj_cone]
% 14.96/2.49  --conj_cone_tolerance                   3.
% 14.96/2.49  --extra_neg_conj                        none
% 14.96/2.49  --large_theory_mode                     true
% 14.96/2.49  --prolific_symb_bound                   200
% 14.96/2.49  --lt_threshold                          2000
% 14.96/2.49  --clause_weak_htbl                      true
% 14.96/2.49  --gc_record_bc_elim                     false
% 14.96/2.49  
% 14.96/2.49  ------ Preprocessing Options
% 14.96/2.49  
% 14.96/2.49  --preprocessing_flag                    true
% 14.96/2.49  --time_out_prep_mult                    0.1
% 14.96/2.49  --splitting_mode                        input
% 14.96/2.49  --splitting_grd                         true
% 14.96/2.49  --splitting_cvd                         false
% 14.96/2.49  --splitting_cvd_svl                     false
% 14.96/2.49  --splitting_nvd                         32
% 14.96/2.49  --sub_typing                            true
% 14.96/2.49  --prep_gs_sim                           true
% 14.96/2.49  --prep_unflatten                        true
% 14.96/2.49  --prep_res_sim                          true
% 14.96/2.49  --prep_upred                            true
% 14.96/2.49  --prep_sem_filter                       exhaustive
% 14.96/2.49  --prep_sem_filter_out                   false
% 14.96/2.49  --pred_elim                             true
% 14.96/2.49  --res_sim_input                         true
% 14.96/2.49  --eq_ax_congr_red                       true
% 14.96/2.49  --pure_diseq_elim                       true
% 14.96/2.49  --brand_transform                       false
% 14.96/2.49  --non_eq_to_eq                          false
% 14.96/2.49  --prep_def_merge                        true
% 14.96/2.49  --prep_def_merge_prop_impl              false
% 14.96/2.49  --prep_def_merge_mbd                    true
% 14.96/2.49  --prep_def_merge_tr_red                 false
% 14.96/2.49  --prep_def_merge_tr_cl                  false
% 14.96/2.49  --smt_preprocessing                     true
% 14.96/2.49  --smt_ac_axioms                         fast
% 14.96/2.49  --preprocessed_out                      false
% 14.96/2.49  --preprocessed_stats                    false
% 14.96/2.49  
% 14.96/2.49  ------ Abstraction refinement Options
% 14.96/2.49  
% 14.96/2.49  --abstr_ref                             []
% 14.96/2.49  --abstr_ref_prep                        false
% 14.96/2.49  --abstr_ref_until_sat                   false
% 14.96/2.49  --abstr_ref_sig_restrict                funpre
% 14.96/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 14.96/2.49  --abstr_ref_under                       []
% 14.96/2.49  
% 14.96/2.49  ------ SAT Options
% 14.96/2.49  
% 14.96/2.49  --sat_mode                              false
% 14.96/2.49  --sat_fm_restart_options                ""
% 14.96/2.49  --sat_gr_def                            false
% 14.96/2.49  --sat_epr_types                         true
% 14.96/2.49  --sat_non_cyclic_types                  false
% 14.96/2.49  --sat_finite_models                     false
% 14.96/2.49  --sat_fm_lemmas                         false
% 14.96/2.49  --sat_fm_prep                           false
% 14.96/2.49  --sat_fm_uc_incr                        true
% 14.96/2.49  --sat_out_model                         small
% 14.96/2.49  --sat_out_clauses                       false
% 14.96/2.49  
% 14.96/2.49  ------ QBF Options
% 14.96/2.49  
% 14.96/2.49  --qbf_mode                              false
% 14.96/2.49  --qbf_elim_univ                         false
% 14.96/2.49  --qbf_dom_inst                          none
% 14.96/2.49  --qbf_dom_pre_inst                      false
% 14.96/2.49  --qbf_sk_in                             false
% 14.96/2.49  --qbf_pred_elim                         true
% 14.96/2.49  --qbf_split                             512
% 14.96/2.49  
% 14.96/2.49  ------ BMC1 Options
% 14.96/2.49  
% 14.96/2.49  --bmc1_incremental                      false
% 14.96/2.49  --bmc1_axioms                           reachable_all
% 14.96/2.49  --bmc1_min_bound                        0
% 14.96/2.49  --bmc1_max_bound                        -1
% 14.96/2.49  --bmc1_max_bound_default                -1
% 14.96/2.49  --bmc1_symbol_reachability              true
% 14.96/2.49  --bmc1_property_lemmas                  false
% 14.96/2.49  --bmc1_k_induction                      false
% 14.96/2.49  --bmc1_non_equiv_states                 false
% 14.96/2.49  --bmc1_deadlock                         false
% 14.96/2.49  --bmc1_ucm                              false
% 14.96/2.49  --bmc1_add_unsat_core                   none
% 14.96/2.49  --bmc1_unsat_core_children              false
% 14.96/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 14.96/2.49  --bmc1_out_stat                         full
% 14.96/2.49  --bmc1_ground_init                      false
% 14.96/2.49  --bmc1_pre_inst_next_state              false
% 14.96/2.49  --bmc1_pre_inst_state                   false
% 14.96/2.49  --bmc1_pre_inst_reach_state             false
% 14.96/2.49  --bmc1_out_unsat_core                   false
% 14.96/2.49  --bmc1_aig_witness_out                  false
% 14.96/2.49  --bmc1_verbose                          false
% 14.96/2.49  --bmc1_dump_clauses_tptp                false
% 14.96/2.49  --bmc1_dump_unsat_core_tptp             false
% 14.96/2.49  --bmc1_dump_file                        -
% 14.96/2.49  --bmc1_ucm_expand_uc_limit              128
% 14.96/2.49  --bmc1_ucm_n_expand_iterations          6
% 14.96/2.49  --bmc1_ucm_extend_mode                  1
% 14.96/2.49  --bmc1_ucm_init_mode                    2
% 14.96/2.49  --bmc1_ucm_cone_mode                    none
% 14.96/2.49  --bmc1_ucm_reduced_relation_type        0
% 14.96/2.49  --bmc1_ucm_relax_model                  4
% 14.96/2.49  --bmc1_ucm_full_tr_after_sat            true
% 14.96/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 14.96/2.49  --bmc1_ucm_layered_model                none
% 14.96/2.49  --bmc1_ucm_max_lemma_size               10
% 14.96/2.49  
% 14.96/2.49  ------ AIG Options
% 14.96/2.49  
% 14.96/2.49  --aig_mode                              false
% 14.96/2.49  
% 14.96/2.49  ------ Instantiation Options
% 14.96/2.49  
% 14.96/2.49  --instantiation_flag                    true
% 14.96/2.49  --inst_sos_flag                         false
% 14.96/2.49  --inst_sos_phase                        true
% 14.96/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.96/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.96/2.49  --inst_lit_sel_side                     num_symb
% 14.96/2.49  --inst_solver_per_active                1400
% 14.96/2.49  --inst_solver_calls_frac                1.
% 14.96/2.49  --inst_passive_queue_type               priority_queues
% 14.96/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.96/2.49  --inst_passive_queues_freq              [25;2]
% 14.96/2.49  --inst_dismatching                      true
% 14.96/2.49  --inst_eager_unprocessed_to_passive     true
% 14.96/2.49  --inst_prop_sim_given                   true
% 14.96/2.49  --inst_prop_sim_new                     false
% 14.96/2.49  --inst_subs_new                         false
% 14.96/2.49  --inst_eq_res_simp                      false
% 14.96/2.49  --inst_subs_given                       false
% 14.96/2.49  --inst_orphan_elimination               true
% 14.96/2.49  --inst_learning_loop_flag               true
% 14.96/2.49  --inst_learning_start                   3000
% 14.96/2.49  --inst_learning_factor                  2
% 14.96/2.49  --inst_start_prop_sim_after_learn       3
% 14.96/2.49  --inst_sel_renew                        solver
% 14.96/2.49  --inst_lit_activity_flag                true
% 14.96/2.49  --inst_restr_to_given                   false
% 14.96/2.49  --inst_activity_threshold               500
% 14.96/2.49  --inst_out_proof                        true
% 14.96/2.49  
% 14.96/2.49  ------ Resolution Options
% 14.96/2.49  
% 14.96/2.49  --resolution_flag                       true
% 14.96/2.49  --res_lit_sel                           adaptive
% 14.96/2.49  --res_lit_sel_side                      none
% 14.96/2.49  --res_ordering                          kbo
% 14.96/2.49  --res_to_prop_solver                    active
% 14.96/2.49  --res_prop_simpl_new                    false
% 14.96/2.49  --res_prop_simpl_given                  true
% 14.96/2.49  --res_passive_queue_type                priority_queues
% 14.96/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.96/2.49  --res_passive_queues_freq               [15;5]
% 14.96/2.49  --res_forward_subs                      full
% 14.96/2.49  --res_backward_subs                     full
% 14.96/2.49  --res_forward_subs_resolution           true
% 14.96/2.49  --res_backward_subs_resolution          true
% 14.96/2.49  --res_orphan_elimination                true
% 14.96/2.49  --res_time_limit                        2.
% 14.96/2.49  --res_out_proof                         true
% 14.96/2.49  
% 14.96/2.49  ------ Superposition Options
% 14.96/2.49  
% 14.96/2.49  --superposition_flag                    true
% 14.96/2.49  --sup_passive_queue_type                priority_queues
% 14.96/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.96/2.49  --sup_passive_queues_freq               [8;1;4]
% 14.96/2.49  --demod_completeness_check              fast
% 14.96/2.49  --demod_use_ground                      true
% 14.96/2.49  --sup_to_prop_solver                    passive
% 14.96/2.49  --sup_prop_simpl_new                    true
% 14.96/2.49  --sup_prop_simpl_given                  true
% 14.96/2.49  --sup_fun_splitting                     false
% 14.96/2.49  --sup_smt_interval                      50000
% 14.96/2.49  
% 14.96/2.49  ------ Superposition Simplification Setup
% 14.96/2.49  
% 14.96/2.49  --sup_indices_passive                   []
% 14.96/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.96/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.96/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.96/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 14.96/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.96/2.49  --sup_full_bw                           [BwDemod]
% 14.96/2.49  --sup_immed_triv                        [TrivRules]
% 14.96/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.96/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.96/2.49  --sup_immed_bw_main                     []
% 14.96/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.96/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 14.96/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.96/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.96/2.49  
% 14.96/2.49  ------ Combination Options
% 14.96/2.49  
% 14.96/2.49  --comb_res_mult                         3
% 14.96/2.49  --comb_sup_mult                         2
% 14.96/2.49  --comb_inst_mult                        10
% 14.96/2.49  
% 14.96/2.49  ------ Debug Options
% 14.96/2.49  
% 14.96/2.49  --dbg_backtrace                         false
% 14.96/2.49  --dbg_dump_prop_clauses                 false
% 14.96/2.49  --dbg_dump_prop_clauses_file            -
% 14.96/2.49  --dbg_out_stat                          false
% 14.96/2.49  ------ Parsing...
% 14.96/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.96/2.49  
% 14.96/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 14.96/2.49  
% 14.96/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.96/2.49  
% 14.96/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.96/2.49  ------ Proving...
% 14.96/2.49  ------ Problem Properties 
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  clauses                                 14
% 14.96/2.49  conjectures                             5
% 14.96/2.49  EPR                                     4
% 14.96/2.49  Horn                                    14
% 14.96/2.49  unary                                   7
% 14.96/2.49  binary                                  3
% 14.96/2.49  lits                                    26
% 14.96/2.49  lits eq                                 6
% 14.96/2.49  fd_pure                                 0
% 14.96/2.49  fd_pseudo                               0
% 14.96/2.49  fd_cond                                 0
% 14.96/2.49  fd_pseudo_cond                          0
% 14.96/2.49  AC symbols                              0
% 14.96/2.49  
% 14.96/2.49  ------ Schedule dynamic 5 is on 
% 14.96/2.49  
% 14.96/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  ------ 
% 14.96/2.49  Current options:
% 14.96/2.49  ------ 
% 14.96/2.49  
% 14.96/2.49  ------ Input Options
% 14.96/2.49  
% 14.96/2.49  --out_options                           all
% 14.96/2.49  --tptp_safe_out                         true
% 14.96/2.49  --problem_path                          ""
% 14.96/2.49  --include_path                          ""
% 14.96/2.49  --clausifier                            res/vclausify_rel
% 14.96/2.49  --clausifier_options                    --mode clausify
% 14.96/2.49  --stdin                                 false
% 14.96/2.49  --stats_out                             all
% 14.96/2.49  
% 14.96/2.49  ------ General Options
% 14.96/2.49  
% 14.96/2.49  --fof                                   false
% 14.96/2.49  --time_out_real                         305.
% 14.96/2.49  --time_out_virtual                      -1.
% 14.96/2.49  --symbol_type_check                     false
% 14.96/2.49  --clausify_out                          false
% 14.96/2.49  --sig_cnt_out                           false
% 14.96/2.49  --trig_cnt_out                          false
% 14.96/2.49  --trig_cnt_out_tolerance                1.
% 14.96/2.49  --trig_cnt_out_sk_spl                   false
% 14.96/2.49  --abstr_cl_out                          false
% 14.96/2.49  
% 14.96/2.49  ------ Global Options
% 14.96/2.49  
% 14.96/2.49  --schedule                              default
% 14.96/2.49  --add_important_lit                     false
% 14.96/2.49  --prop_solver_per_cl                    1000
% 14.96/2.49  --min_unsat_core                        false
% 14.96/2.49  --soft_assumptions                      false
% 14.96/2.49  --soft_lemma_size                       3
% 14.96/2.49  --prop_impl_unit_size                   0
% 14.96/2.49  --prop_impl_unit                        []
% 14.96/2.49  --share_sel_clauses                     true
% 14.96/2.49  --reset_solvers                         false
% 14.96/2.49  --bc_imp_inh                            [conj_cone]
% 14.96/2.49  --conj_cone_tolerance                   3.
% 14.96/2.49  --extra_neg_conj                        none
% 14.96/2.49  --large_theory_mode                     true
% 14.96/2.49  --prolific_symb_bound                   200
% 14.96/2.49  --lt_threshold                          2000
% 14.96/2.49  --clause_weak_htbl                      true
% 14.96/2.49  --gc_record_bc_elim                     false
% 14.96/2.49  
% 14.96/2.49  ------ Preprocessing Options
% 14.96/2.49  
% 14.96/2.49  --preprocessing_flag                    true
% 14.96/2.49  --time_out_prep_mult                    0.1
% 14.96/2.49  --splitting_mode                        input
% 14.96/2.49  --splitting_grd                         true
% 14.96/2.49  --splitting_cvd                         false
% 14.96/2.49  --splitting_cvd_svl                     false
% 14.96/2.49  --splitting_nvd                         32
% 14.96/2.49  --sub_typing                            true
% 14.96/2.49  --prep_gs_sim                           true
% 14.96/2.49  --prep_unflatten                        true
% 14.96/2.49  --prep_res_sim                          true
% 14.96/2.49  --prep_upred                            true
% 14.96/2.49  --prep_sem_filter                       exhaustive
% 14.96/2.49  --prep_sem_filter_out                   false
% 14.96/2.49  --pred_elim                             true
% 14.96/2.49  --res_sim_input                         true
% 14.96/2.49  --eq_ax_congr_red                       true
% 14.96/2.49  --pure_diseq_elim                       true
% 14.96/2.49  --brand_transform                       false
% 14.96/2.49  --non_eq_to_eq                          false
% 14.96/2.49  --prep_def_merge                        true
% 14.96/2.49  --prep_def_merge_prop_impl              false
% 14.96/2.49  --prep_def_merge_mbd                    true
% 14.96/2.49  --prep_def_merge_tr_red                 false
% 14.96/2.49  --prep_def_merge_tr_cl                  false
% 14.96/2.49  --smt_preprocessing                     true
% 14.96/2.49  --smt_ac_axioms                         fast
% 14.96/2.49  --preprocessed_out                      false
% 14.96/2.49  --preprocessed_stats                    false
% 14.96/2.49  
% 14.96/2.49  ------ Abstraction refinement Options
% 14.96/2.49  
% 14.96/2.49  --abstr_ref                             []
% 14.96/2.49  --abstr_ref_prep                        false
% 14.96/2.49  --abstr_ref_until_sat                   false
% 14.96/2.49  --abstr_ref_sig_restrict                funpre
% 14.96/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 14.96/2.49  --abstr_ref_under                       []
% 14.96/2.49  
% 14.96/2.49  ------ SAT Options
% 14.96/2.49  
% 14.96/2.49  --sat_mode                              false
% 14.96/2.49  --sat_fm_restart_options                ""
% 14.96/2.49  --sat_gr_def                            false
% 14.96/2.49  --sat_epr_types                         true
% 14.96/2.49  --sat_non_cyclic_types                  false
% 14.96/2.49  --sat_finite_models                     false
% 14.96/2.49  --sat_fm_lemmas                         false
% 14.96/2.49  --sat_fm_prep                           false
% 14.96/2.49  --sat_fm_uc_incr                        true
% 14.96/2.49  --sat_out_model                         small
% 14.96/2.49  --sat_out_clauses                       false
% 14.96/2.49  
% 14.96/2.49  ------ QBF Options
% 14.96/2.49  
% 14.96/2.49  --qbf_mode                              false
% 14.96/2.49  --qbf_elim_univ                         false
% 14.96/2.49  --qbf_dom_inst                          none
% 14.96/2.49  --qbf_dom_pre_inst                      false
% 14.96/2.49  --qbf_sk_in                             false
% 14.96/2.49  --qbf_pred_elim                         true
% 14.96/2.49  --qbf_split                             512
% 14.96/2.49  
% 14.96/2.49  ------ BMC1 Options
% 14.96/2.49  
% 14.96/2.49  --bmc1_incremental                      false
% 14.96/2.49  --bmc1_axioms                           reachable_all
% 14.96/2.49  --bmc1_min_bound                        0
% 14.96/2.49  --bmc1_max_bound                        -1
% 14.96/2.49  --bmc1_max_bound_default                -1
% 14.96/2.49  --bmc1_symbol_reachability              true
% 14.96/2.49  --bmc1_property_lemmas                  false
% 14.96/2.49  --bmc1_k_induction                      false
% 14.96/2.49  --bmc1_non_equiv_states                 false
% 14.96/2.49  --bmc1_deadlock                         false
% 14.96/2.49  --bmc1_ucm                              false
% 14.96/2.49  --bmc1_add_unsat_core                   none
% 14.96/2.49  --bmc1_unsat_core_children              false
% 14.96/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 14.96/2.49  --bmc1_out_stat                         full
% 14.96/2.49  --bmc1_ground_init                      false
% 14.96/2.49  --bmc1_pre_inst_next_state              false
% 14.96/2.49  --bmc1_pre_inst_state                   false
% 14.96/2.49  --bmc1_pre_inst_reach_state             false
% 14.96/2.49  --bmc1_out_unsat_core                   false
% 14.96/2.49  --bmc1_aig_witness_out                  false
% 14.96/2.49  --bmc1_verbose                          false
% 14.96/2.49  --bmc1_dump_clauses_tptp                false
% 14.96/2.49  --bmc1_dump_unsat_core_tptp             false
% 14.96/2.49  --bmc1_dump_file                        -
% 14.96/2.49  --bmc1_ucm_expand_uc_limit              128
% 14.96/2.49  --bmc1_ucm_n_expand_iterations          6
% 14.96/2.49  --bmc1_ucm_extend_mode                  1
% 14.96/2.49  --bmc1_ucm_init_mode                    2
% 14.96/2.49  --bmc1_ucm_cone_mode                    none
% 14.96/2.49  --bmc1_ucm_reduced_relation_type        0
% 14.96/2.49  --bmc1_ucm_relax_model                  4
% 14.96/2.49  --bmc1_ucm_full_tr_after_sat            true
% 14.96/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 14.96/2.49  --bmc1_ucm_layered_model                none
% 14.96/2.49  --bmc1_ucm_max_lemma_size               10
% 14.96/2.49  
% 14.96/2.49  ------ AIG Options
% 14.96/2.49  
% 14.96/2.49  --aig_mode                              false
% 14.96/2.49  
% 14.96/2.49  ------ Instantiation Options
% 14.96/2.49  
% 14.96/2.49  --instantiation_flag                    true
% 14.96/2.49  --inst_sos_flag                         false
% 14.96/2.49  --inst_sos_phase                        true
% 14.96/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.96/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.96/2.49  --inst_lit_sel_side                     none
% 14.96/2.49  --inst_solver_per_active                1400
% 14.96/2.49  --inst_solver_calls_frac                1.
% 14.96/2.49  --inst_passive_queue_type               priority_queues
% 14.96/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.96/2.49  --inst_passive_queues_freq              [25;2]
% 14.96/2.49  --inst_dismatching                      true
% 14.96/2.49  --inst_eager_unprocessed_to_passive     true
% 14.96/2.49  --inst_prop_sim_given                   true
% 14.96/2.49  --inst_prop_sim_new                     false
% 14.96/2.49  --inst_subs_new                         false
% 14.96/2.49  --inst_eq_res_simp                      false
% 14.96/2.49  --inst_subs_given                       false
% 14.96/2.49  --inst_orphan_elimination               true
% 14.96/2.49  --inst_learning_loop_flag               true
% 14.96/2.49  --inst_learning_start                   3000
% 14.96/2.49  --inst_learning_factor                  2
% 14.96/2.49  --inst_start_prop_sim_after_learn       3
% 14.96/2.49  --inst_sel_renew                        solver
% 14.96/2.49  --inst_lit_activity_flag                true
% 14.96/2.49  --inst_restr_to_given                   false
% 14.96/2.49  --inst_activity_threshold               500
% 14.96/2.49  --inst_out_proof                        true
% 14.96/2.49  
% 14.96/2.49  ------ Resolution Options
% 14.96/2.49  
% 14.96/2.49  --resolution_flag                       false
% 14.96/2.49  --res_lit_sel                           adaptive
% 14.96/2.49  --res_lit_sel_side                      none
% 14.96/2.49  --res_ordering                          kbo
% 14.96/2.49  --res_to_prop_solver                    active
% 14.96/2.49  --res_prop_simpl_new                    false
% 14.96/2.49  --res_prop_simpl_given                  true
% 14.96/2.49  --res_passive_queue_type                priority_queues
% 14.96/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.96/2.49  --res_passive_queues_freq               [15;5]
% 14.96/2.49  --res_forward_subs                      full
% 14.96/2.49  --res_backward_subs                     full
% 14.96/2.49  --res_forward_subs_resolution           true
% 14.96/2.49  --res_backward_subs_resolution          true
% 14.96/2.49  --res_orphan_elimination                true
% 14.96/2.49  --res_time_limit                        2.
% 14.96/2.49  --res_out_proof                         true
% 14.96/2.49  
% 14.96/2.49  ------ Superposition Options
% 14.96/2.49  
% 14.96/2.49  --superposition_flag                    true
% 14.96/2.49  --sup_passive_queue_type                priority_queues
% 14.96/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.96/2.49  --sup_passive_queues_freq               [8;1;4]
% 14.96/2.49  --demod_completeness_check              fast
% 14.96/2.49  --demod_use_ground                      true
% 14.96/2.49  --sup_to_prop_solver                    passive
% 14.96/2.49  --sup_prop_simpl_new                    true
% 14.96/2.49  --sup_prop_simpl_given                  true
% 14.96/2.49  --sup_fun_splitting                     false
% 14.96/2.49  --sup_smt_interval                      50000
% 14.96/2.49  
% 14.96/2.49  ------ Superposition Simplification Setup
% 14.96/2.49  
% 14.96/2.49  --sup_indices_passive                   []
% 14.96/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.96/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.96/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.96/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 14.96/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.96/2.49  --sup_full_bw                           [BwDemod]
% 14.96/2.49  --sup_immed_triv                        [TrivRules]
% 14.96/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.96/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.96/2.49  --sup_immed_bw_main                     []
% 14.96/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.96/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 14.96/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.96/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.96/2.49  
% 14.96/2.49  ------ Combination Options
% 14.96/2.49  
% 14.96/2.49  --comb_res_mult                         3
% 14.96/2.49  --comb_sup_mult                         2
% 14.96/2.49  --comb_inst_mult                        10
% 14.96/2.49  
% 14.96/2.49  ------ Debug Options
% 14.96/2.49  
% 14.96/2.49  --dbg_backtrace                         false
% 14.96/2.49  --dbg_dump_prop_clauses                 false
% 14.96/2.49  --dbg_dump_prop_clauses_file            -
% 14.96/2.49  --dbg_out_stat                          false
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  ------ Proving...
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  % SZS status Theorem for theBenchmark.p
% 14.96/2.49  
% 14.96/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 14.96/2.49  
% 14.96/2.49  fof(f8,conjecture,(
% 14.96/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f9,negated_conjecture,(
% 14.96/2.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 14.96/2.49    inference(negated_conjecture,[],[f8])).
% 14.96/2.49  
% 14.96/2.49  fof(f17,plain,(
% 14.96/2.49    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 14.96/2.49    inference(ennf_transformation,[],[f9])).
% 14.96/2.49  
% 14.96/2.49  fof(f18,plain,(
% 14.96/2.49    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 14.96/2.49    inference(flattening,[],[f17])).
% 14.96/2.49  
% 14.96/2.49  fof(f21,plain,(
% 14.96/2.49    ( ! [X0,X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) => k5_relat_1(k7_relat_1(X0,sK2),k7_relat_1(X1,k9_relat_1(X0,sK2))) != k7_relat_1(k5_relat_1(X0,X1),sK2)) )),
% 14.96/2.49    introduced(choice_axiom,[])).
% 14.96/2.49  
% 14.96/2.49  fof(f20,plain,(
% 14.96/2.49    ( ! [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(sK1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,sK1),X2) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 14.96/2.49    introduced(choice_axiom,[])).
% 14.96/2.49  
% 14.96/2.49  fof(f19,plain,(
% 14.96/2.49    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 14.96/2.49    introduced(choice_axiom,[])).
% 14.96/2.49  
% 14.96/2.49  fof(f22,plain,(
% 14.96/2.49    (k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 14.96/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).
% 14.96/2.49  
% 14.96/2.49  fof(f33,plain,(
% 14.96/2.49    v1_funct_1(sK0)),
% 14.96/2.49    inference(cnf_transformation,[],[f22])).
% 14.96/2.49  
% 14.96/2.49  fof(f7,axiom,(
% 14.96/2.49    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f15,plain,(
% 14.96/2.49    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 14.96/2.49    inference(ennf_transformation,[],[f7])).
% 14.96/2.49  
% 14.96/2.49  fof(f16,plain,(
% 14.96/2.49    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 14.96/2.49    inference(flattening,[],[f15])).
% 14.96/2.49  
% 14.96/2.49  fof(f30,plain,(
% 14.96/2.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 14.96/2.49    inference(cnf_transformation,[],[f16])).
% 14.96/2.49  
% 14.96/2.49  fof(f4,axiom,(
% 14.96/2.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f13,plain,(
% 14.96/2.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 14.96/2.49    inference(ennf_transformation,[],[f4])).
% 14.96/2.49  
% 14.96/2.49  fof(f26,plain,(
% 14.96/2.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 14.96/2.49    inference(cnf_transformation,[],[f13])).
% 14.96/2.49  
% 14.96/2.49  fof(f32,plain,(
% 14.96/2.49    v1_relat_1(sK0)),
% 14.96/2.49    inference(cnf_transformation,[],[f22])).
% 14.96/2.49  
% 14.96/2.49  fof(f2,axiom,(
% 14.96/2.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f11,plain,(
% 14.96/2.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 14.96/2.49    inference(ennf_transformation,[],[f2])).
% 14.96/2.49  
% 14.96/2.49  fof(f24,plain,(
% 14.96/2.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 14.96/2.49    inference(cnf_transformation,[],[f11])).
% 14.96/2.49  
% 14.96/2.49  fof(f6,axiom,(
% 14.96/2.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f28,plain,(
% 14.96/2.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 14.96/2.49    inference(cnf_transformation,[],[f6])).
% 14.96/2.49  
% 14.96/2.49  fof(f1,axiom,(
% 14.96/2.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f10,plain,(
% 14.96/2.49    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 14.96/2.49    inference(ennf_transformation,[],[f1])).
% 14.96/2.49  
% 14.96/2.49  fof(f23,plain,(
% 14.96/2.49    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 14.96/2.49    inference(cnf_transformation,[],[f10])).
% 14.96/2.49  
% 14.96/2.49  fof(f34,plain,(
% 14.96/2.49    v1_relat_1(sK1)),
% 14.96/2.49    inference(cnf_transformation,[],[f22])).
% 14.96/2.49  
% 14.96/2.49  fof(f3,axiom,(
% 14.96/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f12,plain,(
% 14.96/2.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 14.96/2.49    inference(ennf_transformation,[],[f3])).
% 14.96/2.49  
% 14.96/2.49  fof(f25,plain,(
% 14.96/2.49    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 14.96/2.49    inference(cnf_transformation,[],[f12])).
% 14.96/2.49  
% 14.96/2.49  fof(f5,axiom,(
% 14.96/2.49    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 14.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.96/2.49  
% 14.96/2.49  fof(f14,plain,(
% 14.96/2.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 14.96/2.49    inference(ennf_transformation,[],[f5])).
% 14.96/2.49  
% 14.96/2.49  fof(f27,plain,(
% 14.96/2.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 14.96/2.49    inference(cnf_transformation,[],[f14])).
% 14.96/2.49  
% 14.96/2.49  fof(f35,plain,(
% 14.96/2.49    v1_funct_1(sK1)),
% 14.96/2.49    inference(cnf_transformation,[],[f22])).
% 14.96/2.49  
% 14.96/2.49  fof(f36,plain,(
% 14.96/2.49    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 14.96/2.49    inference(cnf_transformation,[],[f22])).
% 14.96/2.49  
% 14.96/2.49  cnf(c_12,negated_conjecture,
% 14.96/2.49      ( v1_funct_1(sK0) ),
% 14.96/2.49      inference(cnf_transformation,[],[f33]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_150,negated_conjecture,
% 14.96/2.49      ( v1_funct_1(sK0) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_12]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_428,plain,
% 14.96/2.49      ( v1_funct_1(sK0) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_8,plain,
% 14.96/2.49      ( ~ v1_funct_1(X0)
% 14.96/2.49      | ~ v1_relat_1(X0)
% 14.96/2.49      | v1_relat_1(k7_relat_1(X0,X1)) ),
% 14.96/2.49      inference(cnf_transformation,[],[f30]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_154,plain,
% 14.96/2.49      ( ~ v1_funct_1(X0_38)
% 14.96/2.49      | ~ v1_relat_1(X0_38)
% 14.96/2.49      | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_8]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_425,plain,
% 14.96/2.49      ( v1_funct_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(k7_relat_1(X0_38,X0_39)) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_3,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0)
% 14.96/2.49      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 14.96/2.49      inference(cnf_transformation,[],[f26]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_159,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0_38)
% 14.96/2.49      | k5_relat_1(X0_38,k6_relat_1(k2_relat_1(X0_38))) = X0_38 ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_3]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_420,plain,
% 14.96/2.49      ( k5_relat_1(X0_38,k6_relat_1(k2_relat_1(X0_38))) = X0_38
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_829,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(X0_38,X0_39),k6_relat_1(k2_relat_1(k7_relat_1(X0_38,X0_39)))) = k7_relat_1(X0_38,X0_39)
% 14.96/2.49      | v1_funct_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_425,c_420]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_6799,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(k2_relat_1(k7_relat_1(sK0,X0_39)))) = k7_relat_1(sK0,X0_39)
% 14.96/2.49      | v1_relat_1(sK0) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_428,c_829]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_13,negated_conjecture,
% 14.96/2.49      ( v1_relat_1(sK0) ),
% 14.96/2.49      inference(cnf_transformation,[],[f32]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_149,negated_conjecture,
% 14.96/2.49      ( v1_relat_1(sK0) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_13]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_429,plain,
% 14.96/2.49      ( v1_relat_1(sK0) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_1,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0)
% 14.96/2.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 14.96/2.49      inference(cnf_transformation,[],[f24]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_161,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0_38)
% 14.96/2.49      | k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_1]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_418,plain,
% 14.96/2.49      ( k2_relat_1(k7_relat_1(X0_38,X0_39)) = k9_relat_1(X0_38,X0_39)
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_687,plain,
% 14.96/2.49      ( k2_relat_1(k7_relat_1(sK0,X0_39)) = k9_relat_1(sK0,X0_39) ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_429,c_418]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_6817,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(k9_relat_1(sK0,X0_39))) = k7_relat_1(sK0,X0_39)
% 14.96/2.49      | v1_relat_1(sK0) != iProver_top ),
% 14.96/2.49      inference(light_normalisation,[status(thm)],[c_6799,c_687]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_6,plain,
% 14.96/2.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 14.96/2.49      inference(cnf_transformation,[],[f28]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_156,plain,
% 14.96/2.49      ( v1_relat_1(k6_relat_1(X0_39)) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_6]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_423,plain,
% 14.96/2.49      ( v1_relat_1(k6_relat_1(X0_39)) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_0,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0)
% 14.96/2.49      | ~ v1_relat_1(X1)
% 14.96/2.49      | k5_relat_1(k7_relat_1(X1,X2),X0) = k7_relat_1(k5_relat_1(X1,X0),X2) ),
% 14.96/2.49      inference(cnf_transformation,[],[f23]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_162,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0_38)
% 14.96/2.49      | ~ v1_relat_1(X1_38)
% 14.96/2.49      | k5_relat_1(k7_relat_1(X1_38,X0_39),X0_38) = k7_relat_1(k5_relat_1(X1_38,X0_38),X0_39) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_0]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_417,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(X0_38,X0_39),X1_38) = k7_relat_1(k5_relat_1(X0_38,X1_38),X0_39)
% 14.96/2.49      | v1_relat_1(X1_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_662,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),X0_38) = k7_relat_1(k5_relat_1(sK0,X0_38),X0_39)
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_429,c_417]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_1528,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(X1_39)) = k7_relat_1(k5_relat_1(sK0,k6_relat_1(X1_39)),X0_39) ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_423,c_662]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_6818,plain,
% 14.96/2.49      ( k7_relat_1(k5_relat_1(sK0,k6_relat_1(k9_relat_1(sK0,X0_39))),X0_39) = k7_relat_1(sK0,X0_39)
% 14.96/2.49      | v1_relat_1(sK0) != iProver_top ),
% 14.96/2.49      inference(demodulation,[status(thm)],[c_6817,c_1528]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_14,plain,
% 14.96/2.49      ( v1_relat_1(sK0) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_39363,plain,
% 14.96/2.49      ( k7_relat_1(k5_relat_1(sK0,k6_relat_1(k9_relat_1(sK0,X0_39))),X0_39) = k7_relat_1(sK0,X0_39) ),
% 14.96/2.49      inference(global_propositional_subsumption,
% 14.96/2.49                [status(thm)],
% 14.96/2.49                [c_6818,c_14]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_11,negated_conjecture,
% 14.96/2.49      ( v1_relat_1(sK1) ),
% 14.96/2.49      inference(cnf_transformation,[],[f34]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_151,negated_conjecture,
% 14.96/2.49      ( v1_relat_1(sK1) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_11]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_427,plain,
% 14.96/2.49      ( v1_relat_1(sK1) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_2,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0)
% 14.96/2.49      | ~ v1_relat_1(X1)
% 14.96/2.49      | ~ v1_relat_1(X2)
% 14.96/2.49      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 14.96/2.49      inference(cnf_transformation,[],[f25]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_160,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0_38)
% 14.96/2.49      | ~ v1_relat_1(X1_38)
% 14.96/2.49      | ~ v1_relat_1(X2_38)
% 14.96/2.49      | k5_relat_1(k5_relat_1(X2_38,X1_38),X0_38) = k5_relat_1(X2_38,k5_relat_1(X1_38,X0_38)) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_2]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_419,plain,
% 14.96/2.49      ( k5_relat_1(k5_relat_1(X0_38,X1_38),X2_38) = k5_relat_1(X0_38,k5_relat_1(X1_38,X2_38))
% 14.96/2.49      | v1_relat_1(X2_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X1_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_1217,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(X0_38,X0_39),k5_relat_1(X1_38,X2_38)) = k5_relat_1(k5_relat_1(k7_relat_1(X0_38,X0_39),X1_38),X2_38)
% 14.96/2.49      | v1_funct_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X1_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X2_38) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_425,c_419]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_8138,plain,
% 14.96/2.49      ( k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),X0_38),X1_38) = k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(X0_38,X1_38))
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X1_38) != iProver_top
% 14.96/2.49      | v1_relat_1(sK0) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_428,c_1217]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_8768,plain,
% 14.96/2.49      ( v1_relat_1(X1_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top
% 14.96/2.49      | k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),X0_38),X1_38) = k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(X0_38,X1_38)) ),
% 14.96/2.49      inference(global_propositional_subsumption,
% 14.96/2.49                [status(thm)],
% 14.96/2.49                [c_8138,c_14]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_8769,plain,
% 14.96/2.49      ( k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),X0_38),X1_38) = k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(X0_38,X1_38))
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X1_38) != iProver_top ),
% 14.96/2.49      inference(renaming,[status(thm)],[c_8768]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_8778,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(k6_relat_1(X1_39),X0_38)) = k5_relat_1(k5_relat_1(k7_relat_1(sK0,X0_39),k6_relat_1(X1_39)),X0_38)
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_423,c_8769]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_8781,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X0_39)),X1_39),X0_38) = k5_relat_1(k7_relat_1(sK0,X1_39),k5_relat_1(k6_relat_1(X0_39),X0_38))
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(light_normalisation,[status(thm)],[c_8778,c_1528]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_66260,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k5_relat_1(k6_relat_1(X1_39),sK1)) = k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X1_39)),X0_39),sK1) ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_427,c_8781]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_4,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0)
% 14.96/2.49      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 14.96/2.49      inference(cnf_transformation,[],[f27]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_158,plain,
% 14.96/2.49      ( ~ v1_relat_1(X0_38)
% 14.96/2.49      | k5_relat_1(k6_relat_1(X0_39),X0_38) = k7_relat_1(X0_38,X0_39) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_4]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_421,plain,
% 14.96/2.49      ( k5_relat_1(k6_relat_1(X0_39),X0_38) = k7_relat_1(X0_38,X0_39)
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_758,plain,
% 14.96/2.49      ( k5_relat_1(k6_relat_1(X0_39),sK1) = k7_relat_1(sK1,X0_39) ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_427,c_421]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_10,negated_conjecture,
% 14.96/2.49      ( v1_funct_1(sK1) ),
% 14.96/2.49      inference(cnf_transformation,[],[f35]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_152,negated_conjecture,
% 14.96/2.49      ( v1_funct_1(sK1) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_10]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_426,plain,
% 14.96/2.49      ( v1_funct_1(sK1) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_152]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_1527,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k7_relat_1(X0_38,X1_39)) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(X0_38,X1_39)),X0_39)
% 14.96/2.49      | v1_funct_1(X0_38) != iProver_top
% 14.96/2.49      | v1_relat_1(X0_38) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_425,c_662]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_4910,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k7_relat_1(sK1,X1_39)) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X1_39)),X0_39)
% 14.96/2.49      | v1_relat_1(sK1) != iProver_top ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_426,c_1527]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_16,plain,
% 14.96/2.49      ( v1_relat_1(sK1) = iProver_top ),
% 14.96/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_5224,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),k7_relat_1(sK1,X1_39)) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X1_39)),X0_39) ),
% 14.96/2.49      inference(global_propositional_subsumption,
% 14.96/2.49                [status(thm)],
% 14.96/2.49                [c_4910,c_16]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_66281,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X0_39)),X1_39),sK1) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X0_39)),X1_39) ),
% 14.96/2.49      inference(demodulation,[status(thm)],[c_66260,c_758,c_5224]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_68497,plain,
% 14.96/2.49      ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0_39))),X0_39) = k5_relat_1(k7_relat_1(sK0,X0_39),sK1) ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_39363,c_66281]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_1525,plain,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,X0_39),sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X0_39) ),
% 14.96/2.49      inference(superposition,[status(thm)],[c_427,c_662]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_68506,plain,
% 14.96/2.49      ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0_39))),X0_39) = k7_relat_1(k5_relat_1(sK0,sK1),X0_39) ),
% 14.96/2.49      inference(light_normalisation,[status(thm)],[c_68497,c_1525]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_68509,plain,
% 14.96/2.49      ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,sK2))),sK2) = k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
% 14.96/2.49      inference(instantiation,[status(thm)],[c_68506]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_9,negated_conjecture,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
% 14.96/2.49      inference(cnf_transformation,[],[f36]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_153,negated_conjecture,
% 14.96/2.49      ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
% 14.96/2.49      inference(subtyping,[status(esa)],[c_9]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(c_5228,plain,
% 14.96/2.49      ( k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,sK2))),sK2) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
% 14.96/2.49      inference(demodulation,[status(thm)],[c_5224,c_153]) ).
% 14.96/2.49  
% 14.96/2.49  cnf(contradiction,plain,
% 14.96/2.49      ( $false ),
% 14.96/2.49      inference(minisat,[status(thm)],[c_68509,c_5228]) ).
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 14.96/2.49  
% 14.96/2.49  ------                               Statistics
% 14.96/2.49  
% 14.96/2.49  ------ General
% 14.96/2.49  
% 14.96/2.49  abstr_ref_over_cycles:                  0
% 14.96/2.49  abstr_ref_under_cycles:                 0
% 14.96/2.49  gc_basic_clause_elim:                   0
% 14.96/2.49  forced_gc_time:                         0
% 14.96/2.49  parsing_time:                           0.008
% 14.96/2.49  unif_index_cands_time:                  0.
% 14.96/2.49  unif_index_add_time:                    0.
% 14.96/2.49  orderings_time:                         0.
% 14.96/2.49  out_proof_time:                         0.009
% 14.96/2.49  total_time:                             1.668
% 14.96/2.49  num_of_symbols:                         43
% 14.96/2.49  num_of_terms:                           25089
% 14.96/2.49  
% 14.96/2.49  ------ Preprocessing
% 14.96/2.49  
% 14.96/2.49  num_of_splits:                          0
% 14.96/2.49  num_of_split_atoms:                     0
% 14.96/2.49  num_of_reused_defs:                     0
% 14.96/2.49  num_eq_ax_congr_red:                    0
% 14.96/2.49  num_of_sem_filtered_clauses:            1
% 14.96/2.49  num_of_subtypes:                        2
% 14.96/2.49  monotx_restored_types:                  0
% 14.96/2.49  sat_num_of_epr_types:                   0
% 14.96/2.49  sat_num_of_non_cyclic_types:            0
% 14.96/2.49  sat_guarded_non_collapsed_types:        1
% 14.96/2.49  num_pure_diseq_elim:                    0
% 14.96/2.49  simp_replaced_by:                       0
% 14.96/2.49  res_preprocessed:                       65
% 14.96/2.49  prep_upred:                             0
% 14.96/2.49  prep_unflattend:                        0
% 14.96/2.49  smt_new_axioms:                         0
% 14.96/2.49  pred_elim_cands:                        2
% 14.96/2.49  pred_elim:                              0
% 14.96/2.49  pred_elim_cl:                           0
% 14.96/2.49  pred_elim_cycles:                       1
% 14.96/2.49  merged_defs:                            0
% 14.96/2.49  merged_defs_ncl:                        0
% 14.96/2.49  bin_hyper_res:                          0
% 14.96/2.49  prep_cycles:                            3
% 14.96/2.49  pred_elim_time:                         0.
% 14.96/2.49  splitting_time:                         0.
% 14.96/2.49  sem_filter_time:                        0.
% 14.96/2.49  monotx_time:                            0.
% 14.96/2.49  subtype_inf_time:                       0.
% 14.96/2.49  
% 14.96/2.49  ------ Problem properties
% 14.96/2.49  
% 14.96/2.49  clauses:                                14
% 14.96/2.49  conjectures:                            5
% 14.96/2.49  epr:                                    4
% 14.96/2.49  horn:                                   14
% 14.96/2.49  ground:                                 5
% 14.96/2.49  unary:                                  7
% 14.96/2.49  binary:                                 3
% 14.96/2.49  lits:                                   26
% 14.96/2.49  lits_eq:                                6
% 14.96/2.49  fd_pure:                                0
% 14.96/2.49  fd_pseudo:                              0
% 14.96/2.49  fd_cond:                                0
% 14.96/2.49  fd_pseudo_cond:                         0
% 14.96/2.49  ac_symbols:                             0
% 14.96/2.49  
% 14.96/2.49  ------ Propositional Solver
% 14.96/2.49  
% 14.96/2.49  prop_solver_calls:                      31
% 14.96/2.49  prop_fast_solver_calls:                 1238
% 14.96/2.49  smt_solver_calls:                       0
% 14.96/2.49  smt_fast_solver_calls:                  0
% 14.96/2.49  prop_num_of_clauses:                    9554
% 14.96/2.49  prop_preprocess_simplified:             25493
% 14.96/2.49  prop_fo_subsumed:                       101
% 14.96/2.49  prop_solver_time:                       0.
% 14.96/2.49  smt_solver_time:                        0.
% 14.96/2.49  smt_fast_solver_time:                   0.
% 14.96/2.49  prop_fast_solver_time:                  0.
% 14.96/2.49  prop_unsat_core_time:                   0.001
% 14.96/2.49  
% 14.96/2.49  ------ QBF
% 14.96/2.49  
% 14.96/2.49  qbf_q_res:                              0
% 14.96/2.49  qbf_num_tautologies:                    0
% 14.96/2.49  qbf_prep_cycles:                        0
% 14.96/2.49  
% 14.96/2.49  ------ BMC1
% 14.96/2.49  
% 14.96/2.49  bmc1_current_bound:                     -1
% 14.96/2.49  bmc1_last_solved_bound:                 -1
% 14.96/2.49  bmc1_unsat_core_size:                   -1
% 14.96/2.49  bmc1_unsat_core_parents_size:           -1
% 14.96/2.49  bmc1_merge_next_fun:                    0
% 14.96/2.49  bmc1_unsat_core_clauses_time:           0.
% 14.96/2.49  
% 14.96/2.49  ------ Instantiation
% 14.96/2.49  
% 14.96/2.49  inst_num_of_clauses:                    5531
% 14.96/2.49  inst_num_in_passive:                    1703
% 14.96/2.49  inst_num_in_active:                     1840
% 14.96/2.49  inst_num_in_unprocessed:                1989
% 14.96/2.49  inst_num_of_loops:                      2200
% 14.96/2.49  inst_num_of_learning_restarts:          0
% 14.96/2.49  inst_num_moves_active_passive:          353
% 14.96/2.49  inst_lit_activity:                      0
% 14.96/2.49  inst_lit_activity_moves:                2
% 14.96/2.49  inst_num_tautologies:                   0
% 14.96/2.49  inst_num_prop_implied:                  0
% 14.96/2.49  inst_num_existing_simplified:           0
% 14.96/2.49  inst_num_eq_res_simplified:             0
% 14.96/2.49  inst_num_child_elim:                    0
% 14.96/2.49  inst_num_of_dismatching_blockings:      13790
% 14.96/2.49  inst_num_of_non_proper_insts:           13424
% 14.96/2.49  inst_num_of_duplicates:                 0
% 14.96/2.49  inst_inst_num_from_inst_to_res:         0
% 14.96/2.49  inst_dismatching_checking_time:         0.
% 14.96/2.49  
% 14.96/2.49  ------ Resolution
% 14.96/2.49  
% 14.96/2.49  res_num_of_clauses:                     0
% 14.96/2.49  res_num_in_passive:                     0
% 14.96/2.49  res_num_in_active:                      0
% 14.96/2.49  res_num_of_loops:                       68
% 14.96/2.49  res_forward_subset_subsumed:            1522
% 14.96/2.49  res_backward_subset_subsumed:           2
% 14.96/2.49  res_forward_subsumed:                   0
% 14.96/2.49  res_backward_subsumed:                  0
% 14.96/2.49  res_forward_subsumption_resolution:     0
% 14.96/2.49  res_backward_subsumption_resolution:    0
% 14.96/2.49  res_clause_to_clause_subsumption:       1807
% 14.96/2.49  res_orphan_elimination:                 0
% 14.96/2.49  res_tautology_del:                      1675
% 14.96/2.49  res_num_eq_res_simplified:              0
% 14.96/2.49  res_num_sel_changes:                    0
% 14.96/2.49  res_moves_from_active_to_pass:          0
% 14.96/2.49  
% 14.96/2.49  ------ Superposition
% 14.96/2.49  
% 14.96/2.49  sup_time_total:                         0.
% 14.96/2.49  sup_time_generating:                    0.
% 14.96/2.49  sup_time_sim_full:                      0.
% 14.96/2.49  sup_time_sim_immed:                     0.
% 14.96/2.49  
% 14.96/2.49  sup_num_of_clauses:                     694
% 14.96/2.49  sup_num_in_active:                      432
% 14.96/2.49  sup_num_in_passive:                     262
% 14.96/2.49  sup_num_of_loops:                       438
% 14.96/2.49  sup_fw_superposition:                   728
% 14.96/2.49  sup_bw_superposition:                   192
% 14.96/2.49  sup_immediate_simplified:               562
% 14.96/2.49  sup_given_eliminated:                   3
% 14.96/2.49  comparisons_done:                       0
% 14.96/2.49  comparisons_avoided:                    0
% 14.96/2.49  
% 14.96/2.49  ------ Simplifications
% 14.96/2.49  
% 14.96/2.49  
% 14.96/2.49  sim_fw_subset_subsumed:                 25
% 14.96/2.49  sim_bw_subset_subsumed:                 18
% 14.96/2.49  sim_fw_subsumed:                        37
% 14.96/2.49  sim_bw_subsumed:                        0
% 14.96/2.49  sim_fw_subsumption_res:                 29
% 14.96/2.49  sim_bw_subsumption_res:                 0
% 14.96/2.49  sim_tautology_del:                      0
% 14.96/2.49  sim_eq_tautology_del:                   104
% 14.96/2.49  sim_eq_res_simp:                        0
% 14.96/2.49  sim_fw_demodulated:                     128
% 14.96/2.49  sim_bw_demodulated:                     6
% 14.96/2.49  sim_light_normalised:                   395
% 14.96/2.49  sim_joinable_taut:                      0
% 14.96/2.49  sim_joinable_simp:                      0
% 14.96/2.49  sim_ac_normalised:                      0
% 14.96/2.49  sim_smt_subsumption:                    0
% 14.96/2.49  
%------------------------------------------------------------------------------
