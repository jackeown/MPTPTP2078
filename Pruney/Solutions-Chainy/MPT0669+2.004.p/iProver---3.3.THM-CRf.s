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
% DateTime   : Thu Dec  3 11:51:10 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 203 expanded)
%              Number of clauses        :   43 (  59 expanded)
%              Number of leaves         :    4 (  32 expanded)
%              Depth                    :   18
%              Number of atoms          :  225 (1049 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_138,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_139,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
    | ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,X0),X1)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_143,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK2))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_139,c_8])).

cnf(c_144,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
    | ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,X0),X1) ),
    inference(renaming,[status(thm)],[c_143])).

cnf(c_225,plain,
    ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41))))
    | ~ r2_hidden(X0_42,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_144])).

cnf(c_369,plain,
    ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41)))) = iProver_top
    | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_169,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_170,plain,
    ( k5_relat_1(sK2,k6_relat_1(X0)) = k8_relat_1(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_224,plain,
    ( k5_relat_1(sK2,k6_relat_1(X0_41)) = k8_relat_1(X0_41,sK2) ),
    inference(subtyping,[status(esa)],[c_170])).

cnf(c_401,plain,
    ( r2_hidden(X0_42,k1_relat_1(k8_relat_1(X0_41,sK2))) = iProver_top
    | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_369,c_224])).

cnf(c_412,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1) != iProver_top
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top
    | r2_hidden(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_230,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_364,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1) != iProver_top
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) != iProver_top
    | r2_hidden(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_102,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_103,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
    | r2_hidden(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_107,plain,
    ( r2_hidden(X0,k1_relat_1(sK2))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_103,c_8])).

cnf(c_108,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
    | r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(renaming,[status(thm)],[c_107])).

cnf(c_227,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41))))
    | r2_hidden(X0_42,k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_108])).

cnf(c_367,plain,
    ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41)))) != iProver_top
    | r2_hidden(X0_42,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_380,plain,
    ( r2_hidden(X0_42,k1_relat_1(k8_relat_1(X0_41,sK2))) != iProver_top
    | r2_hidden(X0_42,k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_367,c_224])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_120,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_121,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
    | r2_hidden(k1_funct_1(sK2,X0),X1)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_120])).

cnf(c_125,plain,
    ( r2_hidden(k1_funct_1(sK2,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_121,c_8])).

cnf(c_126,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
    | r2_hidden(k1_funct_1(sK2,X0),X1) ),
    inference(renaming,[status(thm)],[c_125])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41))))
    | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_126])).

cnf(c_368,plain,
    ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41)))) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_388,plain,
    ( r2_hidden(X0_42,k1_relat_1(k8_relat_1(X0_41,sK2))) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_368,c_224])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_229,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_365,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1) = iProver_top
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_392,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_388,c_365])).

cnf(c_399,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_364,c_380,c_392])).

cnf(c_12,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1) = iProver_top
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_11,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top
    | r2_hidden(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_412,c_399,c_12,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.77/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.77/1.04  
% 0.77/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.77/1.04  
% 0.77/1.04  ------  iProver source info
% 0.77/1.04  
% 0.77/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.77/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.77/1.04  git: non_committed_changes: false
% 0.77/1.04  git: last_make_outside_of_git: false
% 0.77/1.04  
% 0.77/1.04  ------ 
% 0.77/1.04  
% 0.77/1.04  ------ Input Options
% 0.77/1.04  
% 0.77/1.04  --out_options                           all
% 0.77/1.04  --tptp_safe_out                         true
% 0.77/1.04  --problem_path                          ""
% 0.77/1.04  --include_path                          ""
% 0.77/1.04  --clausifier                            res/vclausify_rel
% 0.77/1.04  --clausifier_options                    --mode clausify
% 0.77/1.04  --stdin                                 false
% 0.77/1.04  --stats_out                             all
% 0.77/1.04  
% 0.77/1.04  ------ General Options
% 0.77/1.04  
% 0.77/1.04  --fof                                   false
% 0.77/1.04  --time_out_real                         305.
% 0.77/1.04  --time_out_virtual                      -1.
% 0.77/1.04  --symbol_type_check                     false
% 0.77/1.04  --clausify_out                          false
% 0.77/1.04  --sig_cnt_out                           false
% 0.77/1.04  --trig_cnt_out                          false
% 0.77/1.04  --trig_cnt_out_tolerance                1.
% 0.77/1.04  --trig_cnt_out_sk_spl                   false
% 0.77/1.04  --abstr_cl_out                          false
% 0.77/1.04  
% 0.77/1.04  ------ Global Options
% 0.77/1.04  
% 0.77/1.04  --schedule                              default
% 0.77/1.04  --add_important_lit                     false
% 0.77/1.04  --prop_solver_per_cl                    1000
% 0.77/1.04  --min_unsat_core                        false
% 0.77/1.04  --soft_assumptions                      false
% 0.77/1.04  --soft_lemma_size                       3
% 0.77/1.04  --prop_impl_unit_size                   0
% 0.77/1.04  --prop_impl_unit                        []
% 0.77/1.04  --share_sel_clauses                     true
% 0.77/1.04  --reset_solvers                         false
% 0.77/1.04  --bc_imp_inh                            [conj_cone]
% 0.77/1.04  --conj_cone_tolerance                   3.
% 0.77/1.04  --extra_neg_conj                        none
% 0.77/1.04  --large_theory_mode                     true
% 0.77/1.04  --prolific_symb_bound                   200
% 0.77/1.04  --lt_threshold                          2000
% 0.77/1.04  --clause_weak_htbl                      true
% 0.77/1.04  --gc_record_bc_elim                     false
% 0.77/1.04  
% 0.77/1.04  ------ Preprocessing Options
% 0.77/1.04  
% 0.77/1.04  --preprocessing_flag                    true
% 0.77/1.04  --time_out_prep_mult                    0.1
% 0.77/1.04  --splitting_mode                        input
% 0.77/1.04  --splitting_grd                         true
% 0.77/1.04  --splitting_cvd                         false
% 0.77/1.04  --splitting_cvd_svl                     false
% 0.77/1.04  --splitting_nvd                         32
% 0.77/1.04  --sub_typing                            true
% 0.77/1.04  --prep_gs_sim                           true
% 0.77/1.04  --prep_unflatten                        true
% 0.77/1.04  --prep_res_sim                          true
% 0.77/1.04  --prep_upred                            true
% 0.77/1.04  --prep_sem_filter                       exhaustive
% 0.77/1.04  --prep_sem_filter_out                   false
% 0.77/1.04  --pred_elim                             true
% 0.77/1.04  --res_sim_input                         true
% 0.77/1.04  --eq_ax_congr_red                       true
% 0.77/1.04  --pure_diseq_elim                       true
% 0.77/1.04  --brand_transform                       false
% 0.77/1.04  --non_eq_to_eq                          false
% 0.77/1.04  --prep_def_merge                        true
% 0.77/1.04  --prep_def_merge_prop_impl              false
% 0.77/1.04  --prep_def_merge_mbd                    true
% 0.77/1.04  --prep_def_merge_tr_red                 false
% 0.77/1.04  --prep_def_merge_tr_cl                  false
% 0.77/1.04  --smt_preprocessing                     true
% 0.77/1.04  --smt_ac_axioms                         fast
% 0.77/1.04  --preprocessed_out                      false
% 0.77/1.04  --preprocessed_stats                    false
% 0.77/1.04  
% 0.77/1.04  ------ Abstraction refinement Options
% 0.77/1.04  
% 0.77/1.04  --abstr_ref                             []
% 0.77/1.04  --abstr_ref_prep                        false
% 0.77/1.04  --abstr_ref_until_sat                   false
% 0.77/1.04  --abstr_ref_sig_restrict                funpre
% 0.77/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.77/1.04  --abstr_ref_under                       []
% 0.77/1.04  
% 0.77/1.04  ------ SAT Options
% 0.77/1.04  
% 0.77/1.04  --sat_mode                              false
% 0.77/1.04  --sat_fm_restart_options                ""
% 0.77/1.04  --sat_gr_def                            false
% 0.77/1.04  --sat_epr_types                         true
% 0.77/1.04  --sat_non_cyclic_types                  false
% 0.77/1.04  --sat_finite_models                     false
% 0.77/1.04  --sat_fm_lemmas                         false
% 0.77/1.04  --sat_fm_prep                           false
% 0.77/1.04  --sat_fm_uc_incr                        true
% 0.77/1.04  --sat_out_model                         small
% 0.77/1.04  --sat_out_clauses                       false
% 0.77/1.04  
% 0.77/1.04  ------ QBF Options
% 0.77/1.04  
% 0.77/1.04  --qbf_mode                              false
% 0.77/1.04  --qbf_elim_univ                         false
% 0.77/1.04  --qbf_dom_inst                          none
% 0.77/1.04  --qbf_dom_pre_inst                      false
% 0.77/1.04  --qbf_sk_in                             false
% 0.77/1.04  --qbf_pred_elim                         true
% 0.77/1.04  --qbf_split                             512
% 0.77/1.04  
% 0.77/1.04  ------ BMC1 Options
% 0.77/1.04  
% 0.77/1.04  --bmc1_incremental                      false
% 0.77/1.04  --bmc1_axioms                           reachable_all
% 0.77/1.04  --bmc1_min_bound                        0
% 0.77/1.04  --bmc1_max_bound                        -1
% 0.77/1.04  --bmc1_max_bound_default                -1
% 0.77/1.04  --bmc1_symbol_reachability              true
% 0.77/1.04  --bmc1_property_lemmas                  false
% 0.77/1.04  --bmc1_k_induction                      false
% 0.77/1.04  --bmc1_non_equiv_states                 false
% 0.77/1.04  --bmc1_deadlock                         false
% 0.77/1.04  --bmc1_ucm                              false
% 0.77/1.04  --bmc1_add_unsat_core                   none
% 0.77/1.04  --bmc1_unsat_core_children              false
% 0.77/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.77/1.04  --bmc1_out_stat                         full
% 0.77/1.04  --bmc1_ground_init                      false
% 0.77/1.04  --bmc1_pre_inst_next_state              false
% 0.77/1.04  --bmc1_pre_inst_state                   false
% 0.77/1.04  --bmc1_pre_inst_reach_state             false
% 0.77/1.04  --bmc1_out_unsat_core                   false
% 0.77/1.04  --bmc1_aig_witness_out                  false
% 0.77/1.04  --bmc1_verbose                          false
% 0.77/1.04  --bmc1_dump_clauses_tptp                false
% 0.77/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.77/1.04  --bmc1_dump_file                        -
% 0.77/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.77/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.77/1.04  --bmc1_ucm_extend_mode                  1
% 0.77/1.04  --bmc1_ucm_init_mode                    2
% 0.77/1.04  --bmc1_ucm_cone_mode                    none
% 0.77/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.77/1.04  --bmc1_ucm_relax_model                  4
% 0.77/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.77/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.77/1.04  --bmc1_ucm_layered_model                none
% 0.77/1.04  --bmc1_ucm_max_lemma_size               10
% 0.77/1.04  
% 0.77/1.04  ------ AIG Options
% 0.77/1.04  
% 0.77/1.04  --aig_mode                              false
% 0.77/1.04  
% 0.77/1.04  ------ Instantiation Options
% 0.77/1.04  
% 0.77/1.04  --instantiation_flag                    true
% 0.77/1.04  --inst_sos_flag                         false
% 0.77/1.04  --inst_sos_phase                        true
% 0.77/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.77/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.77/1.04  --inst_lit_sel_side                     num_symb
% 0.77/1.04  --inst_solver_per_active                1400
% 0.77/1.04  --inst_solver_calls_frac                1.
% 0.77/1.04  --inst_passive_queue_type               priority_queues
% 0.77/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.77/1.04  --inst_passive_queues_freq              [25;2]
% 0.77/1.04  --inst_dismatching                      true
% 0.77/1.04  --inst_eager_unprocessed_to_passive     true
% 0.77/1.04  --inst_prop_sim_given                   true
% 0.77/1.04  --inst_prop_sim_new                     false
% 0.77/1.04  --inst_subs_new                         false
% 0.77/1.04  --inst_eq_res_simp                      false
% 0.77/1.04  --inst_subs_given                       false
% 0.77/1.04  --inst_orphan_elimination               true
% 0.77/1.04  --inst_learning_loop_flag               true
% 0.77/1.04  --inst_learning_start                   3000
% 0.77/1.04  --inst_learning_factor                  2
% 0.77/1.04  --inst_start_prop_sim_after_learn       3
% 0.77/1.04  --inst_sel_renew                        solver
% 0.77/1.04  --inst_lit_activity_flag                true
% 0.77/1.04  --inst_restr_to_given                   false
% 0.77/1.04  --inst_activity_threshold               500
% 0.77/1.04  --inst_out_proof                        true
% 0.77/1.04  
% 0.77/1.04  ------ Resolution Options
% 0.77/1.04  
% 0.77/1.04  --resolution_flag                       true
% 0.77/1.04  --res_lit_sel                           adaptive
% 0.77/1.04  --res_lit_sel_side                      none
% 0.77/1.04  --res_ordering                          kbo
% 0.77/1.04  --res_to_prop_solver                    active
% 0.77/1.04  --res_prop_simpl_new                    false
% 0.77/1.04  --res_prop_simpl_given                  true
% 0.77/1.04  --res_passive_queue_type                priority_queues
% 0.77/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.77/1.04  --res_passive_queues_freq               [15;5]
% 0.77/1.04  --res_forward_subs                      full
% 0.77/1.04  --res_backward_subs                     full
% 0.77/1.04  --res_forward_subs_resolution           true
% 0.77/1.04  --res_backward_subs_resolution          true
% 0.77/1.04  --res_orphan_elimination                true
% 0.77/1.04  --res_time_limit                        2.
% 0.77/1.04  --res_out_proof                         true
% 0.77/1.04  
% 0.77/1.04  ------ Superposition Options
% 0.77/1.04  
% 0.77/1.04  --superposition_flag                    true
% 0.77/1.04  --sup_passive_queue_type                priority_queues
% 0.77/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.77/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.77/1.04  --demod_completeness_check              fast
% 0.77/1.04  --demod_use_ground                      true
% 0.77/1.04  --sup_to_prop_solver                    passive
% 0.77/1.04  --sup_prop_simpl_new                    true
% 0.77/1.04  --sup_prop_simpl_given                  true
% 0.77/1.04  --sup_fun_splitting                     false
% 0.77/1.04  --sup_smt_interval                      50000
% 0.77/1.04  
% 0.77/1.04  ------ Superposition Simplification Setup
% 0.77/1.04  
% 0.77/1.04  --sup_indices_passive                   []
% 0.77/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.77/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_full_bw                           [BwDemod]
% 0.77/1.04  --sup_immed_triv                        [TrivRules]
% 0.77/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.77/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_immed_bw_main                     []
% 0.77/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.77/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.04  
% 0.77/1.04  ------ Combination Options
% 0.77/1.04  
% 0.77/1.04  --comb_res_mult                         3
% 0.77/1.04  --comb_sup_mult                         2
% 0.77/1.04  --comb_inst_mult                        10
% 0.77/1.04  
% 0.77/1.04  ------ Debug Options
% 0.77/1.04  
% 0.77/1.04  --dbg_backtrace                         false
% 0.77/1.04  --dbg_dump_prop_clauses                 false
% 0.77/1.04  --dbg_dump_prop_clauses_file            -
% 0.77/1.04  --dbg_out_stat                          false
% 0.77/1.04  ------ Parsing...
% 0.77/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.77/1.04  
% 0.77/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.77/1.04  
% 0.77/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.77/1.04  
% 0.77/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.77/1.04  ------ Proving...
% 0.77/1.04  ------ Problem Properties 
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  clauses                                 7
% 0.77/1.04  conjectures                             3
% 0.77/1.04  EPR                                     0
% 0.77/1.04  Horn                                    5
% 0.77/1.04  unary                                   1
% 0.77/1.04  binary                                  4
% 0.77/1.04  lits                                    15
% 0.77/1.04  lits eq                                 1
% 0.77/1.04  fd_pure                                 0
% 0.77/1.04  fd_pseudo                               0
% 0.77/1.04  fd_cond                                 0
% 0.77/1.04  fd_pseudo_cond                          0
% 0.77/1.04  AC symbols                              0
% 0.77/1.04  
% 0.77/1.04  ------ Schedule dynamic 5 is on 
% 0.77/1.04  
% 0.77/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  ------ 
% 0.77/1.04  Current options:
% 0.77/1.04  ------ 
% 0.77/1.04  
% 0.77/1.04  ------ Input Options
% 0.77/1.04  
% 0.77/1.04  --out_options                           all
% 0.77/1.04  --tptp_safe_out                         true
% 0.77/1.04  --problem_path                          ""
% 0.77/1.04  --include_path                          ""
% 0.77/1.04  --clausifier                            res/vclausify_rel
% 0.77/1.04  --clausifier_options                    --mode clausify
% 0.77/1.04  --stdin                                 false
% 0.77/1.04  --stats_out                             all
% 0.77/1.04  
% 0.77/1.04  ------ General Options
% 0.77/1.04  
% 0.77/1.04  --fof                                   false
% 0.77/1.04  --time_out_real                         305.
% 0.77/1.04  --time_out_virtual                      -1.
% 0.77/1.04  --symbol_type_check                     false
% 0.77/1.04  --clausify_out                          false
% 0.77/1.04  --sig_cnt_out                           false
% 0.77/1.04  --trig_cnt_out                          false
% 0.77/1.04  --trig_cnt_out_tolerance                1.
% 0.77/1.04  --trig_cnt_out_sk_spl                   false
% 0.77/1.04  --abstr_cl_out                          false
% 0.77/1.04  
% 0.77/1.04  ------ Global Options
% 0.77/1.04  
% 0.77/1.04  --schedule                              default
% 0.77/1.04  --add_important_lit                     false
% 0.77/1.04  --prop_solver_per_cl                    1000
% 0.77/1.04  --min_unsat_core                        false
% 0.77/1.04  --soft_assumptions                      false
% 0.77/1.04  --soft_lemma_size                       3
% 0.77/1.04  --prop_impl_unit_size                   0
% 0.77/1.04  --prop_impl_unit                        []
% 0.77/1.04  --share_sel_clauses                     true
% 0.77/1.04  --reset_solvers                         false
% 0.77/1.04  --bc_imp_inh                            [conj_cone]
% 0.77/1.04  --conj_cone_tolerance                   3.
% 0.77/1.04  --extra_neg_conj                        none
% 0.77/1.04  --large_theory_mode                     true
% 0.77/1.04  --prolific_symb_bound                   200
% 0.77/1.04  --lt_threshold                          2000
% 0.77/1.04  --clause_weak_htbl                      true
% 0.77/1.04  --gc_record_bc_elim                     false
% 0.77/1.04  
% 0.77/1.04  ------ Preprocessing Options
% 0.77/1.04  
% 0.77/1.04  --preprocessing_flag                    true
% 0.77/1.04  --time_out_prep_mult                    0.1
% 0.77/1.04  --splitting_mode                        input
% 0.77/1.04  --splitting_grd                         true
% 0.77/1.04  --splitting_cvd                         false
% 0.77/1.04  --splitting_cvd_svl                     false
% 0.77/1.04  --splitting_nvd                         32
% 0.77/1.04  --sub_typing                            true
% 0.77/1.04  --prep_gs_sim                           true
% 0.77/1.04  --prep_unflatten                        true
% 0.77/1.04  --prep_res_sim                          true
% 0.77/1.04  --prep_upred                            true
% 0.77/1.04  --prep_sem_filter                       exhaustive
% 0.77/1.04  --prep_sem_filter_out                   false
% 0.77/1.04  --pred_elim                             true
% 0.77/1.04  --res_sim_input                         true
% 0.77/1.04  --eq_ax_congr_red                       true
% 0.77/1.04  --pure_diseq_elim                       true
% 0.77/1.04  --brand_transform                       false
% 0.77/1.04  --non_eq_to_eq                          false
% 0.77/1.04  --prep_def_merge                        true
% 0.77/1.04  --prep_def_merge_prop_impl              false
% 0.77/1.04  --prep_def_merge_mbd                    true
% 0.77/1.04  --prep_def_merge_tr_red                 false
% 0.77/1.04  --prep_def_merge_tr_cl                  false
% 0.77/1.04  --smt_preprocessing                     true
% 0.77/1.04  --smt_ac_axioms                         fast
% 0.77/1.04  --preprocessed_out                      false
% 0.77/1.04  --preprocessed_stats                    false
% 0.77/1.04  
% 0.77/1.04  ------ Abstraction refinement Options
% 0.77/1.04  
% 0.77/1.04  --abstr_ref                             []
% 0.77/1.04  --abstr_ref_prep                        false
% 0.77/1.04  --abstr_ref_until_sat                   false
% 0.77/1.04  --abstr_ref_sig_restrict                funpre
% 0.77/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.77/1.04  --abstr_ref_under                       []
% 0.77/1.04  
% 0.77/1.04  ------ SAT Options
% 0.77/1.04  
% 0.77/1.04  --sat_mode                              false
% 0.77/1.04  --sat_fm_restart_options                ""
% 0.77/1.04  --sat_gr_def                            false
% 0.77/1.04  --sat_epr_types                         true
% 0.77/1.04  --sat_non_cyclic_types                  false
% 0.77/1.04  --sat_finite_models                     false
% 0.77/1.04  --sat_fm_lemmas                         false
% 0.77/1.04  --sat_fm_prep                           false
% 0.77/1.04  --sat_fm_uc_incr                        true
% 0.77/1.04  --sat_out_model                         small
% 0.77/1.04  --sat_out_clauses                       false
% 0.77/1.04  
% 0.77/1.04  ------ QBF Options
% 0.77/1.04  
% 0.77/1.04  --qbf_mode                              false
% 0.77/1.04  --qbf_elim_univ                         false
% 0.77/1.04  --qbf_dom_inst                          none
% 0.77/1.04  --qbf_dom_pre_inst                      false
% 0.77/1.04  --qbf_sk_in                             false
% 0.77/1.04  --qbf_pred_elim                         true
% 0.77/1.04  --qbf_split                             512
% 0.77/1.04  
% 0.77/1.04  ------ BMC1 Options
% 0.77/1.04  
% 0.77/1.04  --bmc1_incremental                      false
% 0.77/1.04  --bmc1_axioms                           reachable_all
% 0.77/1.04  --bmc1_min_bound                        0
% 0.77/1.04  --bmc1_max_bound                        -1
% 0.77/1.04  --bmc1_max_bound_default                -1
% 0.77/1.04  --bmc1_symbol_reachability              true
% 0.77/1.04  --bmc1_property_lemmas                  false
% 0.77/1.04  --bmc1_k_induction                      false
% 0.77/1.04  --bmc1_non_equiv_states                 false
% 0.77/1.04  --bmc1_deadlock                         false
% 0.77/1.04  --bmc1_ucm                              false
% 0.77/1.04  --bmc1_add_unsat_core                   none
% 0.77/1.04  --bmc1_unsat_core_children              false
% 0.77/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.77/1.04  --bmc1_out_stat                         full
% 0.77/1.04  --bmc1_ground_init                      false
% 0.77/1.04  --bmc1_pre_inst_next_state              false
% 0.77/1.04  --bmc1_pre_inst_state                   false
% 0.77/1.04  --bmc1_pre_inst_reach_state             false
% 0.77/1.04  --bmc1_out_unsat_core                   false
% 0.77/1.04  --bmc1_aig_witness_out                  false
% 0.77/1.04  --bmc1_verbose                          false
% 0.77/1.04  --bmc1_dump_clauses_tptp                false
% 0.77/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.77/1.04  --bmc1_dump_file                        -
% 0.77/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.77/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.77/1.04  --bmc1_ucm_extend_mode                  1
% 0.77/1.04  --bmc1_ucm_init_mode                    2
% 0.77/1.04  --bmc1_ucm_cone_mode                    none
% 0.77/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.77/1.04  --bmc1_ucm_relax_model                  4
% 0.77/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.77/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.77/1.04  --bmc1_ucm_layered_model                none
% 0.77/1.04  --bmc1_ucm_max_lemma_size               10
% 0.77/1.04  
% 0.77/1.04  ------ AIG Options
% 0.77/1.04  
% 0.77/1.04  --aig_mode                              false
% 0.77/1.04  
% 0.77/1.04  ------ Instantiation Options
% 0.77/1.04  
% 0.77/1.04  --instantiation_flag                    true
% 0.77/1.04  --inst_sos_flag                         false
% 0.77/1.04  --inst_sos_phase                        true
% 0.77/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.77/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.77/1.04  --inst_lit_sel_side                     none
% 0.77/1.04  --inst_solver_per_active                1400
% 0.77/1.04  --inst_solver_calls_frac                1.
% 0.77/1.04  --inst_passive_queue_type               priority_queues
% 0.77/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.77/1.04  --inst_passive_queues_freq              [25;2]
% 0.77/1.04  --inst_dismatching                      true
% 0.77/1.04  --inst_eager_unprocessed_to_passive     true
% 0.77/1.04  --inst_prop_sim_given                   true
% 0.77/1.04  --inst_prop_sim_new                     false
% 0.77/1.04  --inst_subs_new                         false
% 0.77/1.04  --inst_eq_res_simp                      false
% 0.77/1.04  --inst_subs_given                       false
% 0.77/1.04  --inst_orphan_elimination               true
% 0.77/1.04  --inst_learning_loop_flag               true
% 0.77/1.04  --inst_learning_start                   3000
% 0.77/1.04  --inst_learning_factor                  2
% 0.77/1.04  --inst_start_prop_sim_after_learn       3
% 0.77/1.04  --inst_sel_renew                        solver
% 0.77/1.04  --inst_lit_activity_flag                true
% 0.77/1.04  --inst_restr_to_given                   false
% 0.77/1.04  --inst_activity_threshold               500
% 0.77/1.04  --inst_out_proof                        true
% 0.77/1.04  
% 0.77/1.04  ------ Resolution Options
% 0.77/1.04  
% 0.77/1.04  --resolution_flag                       false
% 0.77/1.04  --res_lit_sel                           adaptive
% 0.77/1.04  --res_lit_sel_side                      none
% 0.77/1.04  --res_ordering                          kbo
% 0.77/1.04  --res_to_prop_solver                    active
% 0.77/1.04  --res_prop_simpl_new                    false
% 0.77/1.04  --res_prop_simpl_given                  true
% 0.77/1.04  --res_passive_queue_type                priority_queues
% 0.77/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.77/1.04  --res_passive_queues_freq               [15;5]
% 0.77/1.04  --res_forward_subs                      full
% 0.77/1.04  --res_backward_subs                     full
% 0.77/1.04  --res_forward_subs_resolution           true
% 0.77/1.04  --res_backward_subs_resolution          true
% 0.77/1.04  --res_orphan_elimination                true
% 0.77/1.04  --res_time_limit                        2.
% 0.77/1.04  --res_out_proof                         true
% 0.77/1.04  
% 0.77/1.04  ------ Superposition Options
% 0.77/1.04  
% 0.77/1.04  --superposition_flag                    true
% 0.77/1.04  --sup_passive_queue_type                priority_queues
% 0.77/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.77/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.77/1.04  --demod_completeness_check              fast
% 0.77/1.04  --demod_use_ground                      true
% 0.77/1.04  --sup_to_prop_solver                    passive
% 0.77/1.04  --sup_prop_simpl_new                    true
% 0.77/1.04  --sup_prop_simpl_given                  true
% 0.77/1.04  --sup_fun_splitting                     false
% 0.77/1.04  --sup_smt_interval                      50000
% 0.77/1.04  
% 0.77/1.04  ------ Superposition Simplification Setup
% 0.77/1.04  
% 0.77/1.04  --sup_indices_passive                   []
% 0.77/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.77/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_full_bw                           [BwDemod]
% 0.77/1.04  --sup_immed_triv                        [TrivRules]
% 0.77/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.77/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_immed_bw_main                     []
% 0.77/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.77/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/1.04  
% 0.77/1.04  ------ Combination Options
% 0.77/1.04  
% 0.77/1.04  --comb_res_mult                         3
% 0.77/1.04  --comb_sup_mult                         2
% 0.77/1.04  --comb_inst_mult                        10
% 0.77/1.04  
% 0.77/1.04  ------ Debug Options
% 0.77/1.04  
% 0.77/1.04  --dbg_backtrace                         false
% 0.77/1.04  --dbg_dump_prop_clauses                 false
% 0.77/1.04  --dbg_dump_prop_clauses_file            -
% 0.77/1.04  --dbg_out_stat                          false
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  ------ Proving...
% 0.77/1.04  
% 0.77/1.04  
% 0.77/1.04  % SZS status Theorem for theBenchmark.p
% 0.77/1.04  
% 0.77/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.77/1.04  
% 0.77/1.04  fof(f2,axiom,(
% 0.77/1.04    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f6,plain,(
% 0.77/1.04    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.77/1.04    inference(ennf_transformation,[],[f2])).
% 0.77/1.04  
% 0.77/1.04  fof(f7,plain,(
% 0.77/1.04    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.77/1.04    inference(flattening,[],[f6])).
% 0.77/1.04  
% 0.77/1.04  fof(f10,plain,(
% 0.77/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.77/1.04    inference(nnf_transformation,[],[f7])).
% 0.77/1.04  
% 0.77/1.04  fof(f11,plain,(
% 0.77/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.77/1.04    inference(flattening,[],[f10])).
% 0.77/1.04  
% 0.77/1.04  fof(f19,plain,(
% 0.77/1.04    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.77/1.04    inference(cnf_transformation,[],[f11])).
% 0.77/1.04  
% 0.77/1.04  fof(f3,conjecture,(
% 0.77/1.04    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.77/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.04  
% 0.77/1.04  fof(f4,negated_conjecture,(
% 0.77/1.04    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.77/1.04    inference(negated_conjecture,[],[f3])).
% 0.77/1.04  
% 0.77/1.04  fof(f8,plain,(
% 0.77/1.04    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.77/1.04    inference(ennf_transformation,[],[f4])).
% 0.77/1.04  
% 0.77/1.04  fof(f9,plain,(
% 0.77/1.04    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.77/1.04    inference(flattening,[],[f8])).
% 0.77/1.04  
% 0.77/1.04  fof(f12,plain,(
% 0.77/1.04    ? [X0,X1,X2] : ((((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.77/1.04    inference(nnf_transformation,[],[f9])).
% 0.77/1.04  
% 0.77/1.04  fof(f13,plain,(
% 0.77/1.04    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.77/1.04    inference(flattening,[],[f12])).
% 0.77/1.04  
% 0.77/1.04  fof(f14,plain,(
% 0.77/1.04    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.77/1.04    introduced(choice_axiom,[])).
% 0.77/1.04  
% 0.77/1.04  fof(f15,plain,(
% 0.77/1.04    (~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.77/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.77/1.05  
% 0.77/1.05  fof(f21,plain,(
% 0.77/1.05    v1_funct_1(sK2)),
% 0.77/1.05    inference(cnf_transformation,[],[f15])).
% 0.77/1.05  
% 0.77/1.05  fof(f20,plain,(
% 0.77/1.05    v1_relat_1(sK2)),
% 0.77/1.05    inference(cnf_transformation,[],[f15])).
% 0.77/1.05  
% 0.77/1.05  fof(f1,axiom,(
% 0.77/1.05    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.77/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.77/1.05  
% 0.77/1.05  fof(f5,plain,(
% 0.77/1.05    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.77/1.05    inference(ennf_transformation,[],[f1])).
% 0.77/1.05  
% 0.77/1.05  fof(f16,plain,(
% 0.77/1.05    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.77/1.05    inference(cnf_transformation,[],[f5])).
% 0.77/1.05  
% 0.77/1.05  fof(f24,plain,(
% 0.77/1.05    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.77/1.05    inference(cnf_transformation,[],[f15])).
% 0.77/1.05  
% 0.77/1.05  fof(f17,plain,(
% 0.77/1.05    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.77/1.05    inference(cnf_transformation,[],[f11])).
% 0.77/1.05  
% 0.77/1.05  fof(f18,plain,(
% 0.77/1.05    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.77/1.05    inference(cnf_transformation,[],[f11])).
% 0.77/1.05  
% 0.77/1.05  fof(f23,plain,(
% 0.77/1.05    r2_hidden(k1_funct_1(sK2,sK0),sK1) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.77/1.05    inference(cnf_transformation,[],[f15])).
% 0.77/1.05  
% 0.77/1.05  fof(f22,plain,(
% 0.77/1.05    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.77/1.05    inference(cnf_transformation,[],[f15])).
% 0.77/1.05  
% 0.77/1.05  cnf(c_1,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 0.77/1.05      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 0.77/1.05      | ~ r2_hidden(k1_funct_1(X1,X0),X2)
% 0.77/1.05      | ~ v1_funct_1(X1)
% 0.77/1.05      | ~ v1_relat_1(X1) ),
% 0.77/1.05      inference(cnf_transformation,[],[f19]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_7,negated_conjecture,
% 0.77/1.05      ( v1_funct_1(sK2) ),
% 0.77/1.05      inference(cnf_transformation,[],[f21]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_138,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 0.77/1.05      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 0.77/1.05      | ~ r2_hidden(k1_funct_1(X1,X0),X2)
% 0.77/1.05      | ~ v1_relat_1(X1)
% 0.77/1.05      | sK2 != X1 ),
% 0.77/1.05      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_139,plain,
% 0.77/1.05      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
% 0.77/1.05      | ~ r2_hidden(X0,k1_relat_1(sK2))
% 0.77/1.05      | ~ r2_hidden(k1_funct_1(sK2,X0),X1)
% 0.77/1.05      | ~ v1_relat_1(sK2) ),
% 0.77/1.05      inference(unflattening,[status(thm)],[c_138]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_8,negated_conjecture,
% 0.77/1.05      ( v1_relat_1(sK2) ),
% 0.77/1.05      inference(cnf_transformation,[],[f20]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_143,plain,
% 0.77/1.05      ( ~ r2_hidden(k1_funct_1(sK2,X0),X1)
% 0.77/1.05      | ~ r2_hidden(X0,k1_relat_1(sK2))
% 0.77/1.05      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ),
% 0.77/1.05      inference(global_propositional_subsumption,
% 0.77/1.05                [status(thm)],
% 0.77/1.05                [c_139,c_8]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_144,plain,
% 0.77/1.05      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
% 0.77/1.05      | ~ r2_hidden(X0,k1_relat_1(sK2))
% 0.77/1.05      | ~ r2_hidden(k1_funct_1(sK2,X0),X1) ),
% 0.77/1.05      inference(renaming,[status(thm)],[c_143]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_225,plain,
% 0.77/1.05      ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41))))
% 0.77/1.05      | ~ r2_hidden(X0_42,k1_relat_1(sK2))
% 0.77/1.05      | ~ r2_hidden(k1_funct_1(sK2,X0_42),X0_41) ),
% 0.77/1.05      inference(subtyping,[status(esa)],[c_144]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_369,plain,
% 0.77/1.05      ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41)))) = iProver_top
% 0.77/1.05      | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
% 0.77/1.05      | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) != iProver_top ),
% 0.77/1.05      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_0,plain,
% 0.77/1.05      ( ~ v1_relat_1(X0)
% 0.77/1.05      | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 0.77/1.05      inference(cnf_transformation,[],[f16]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_169,plain,
% 0.77/1.05      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) | sK2 != X0 ),
% 0.77/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_170,plain,
% 0.77/1.05      ( k5_relat_1(sK2,k6_relat_1(X0)) = k8_relat_1(X0,sK2) ),
% 0.77/1.05      inference(unflattening,[status(thm)],[c_169]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_224,plain,
% 0.77/1.05      ( k5_relat_1(sK2,k6_relat_1(X0_41)) = k8_relat_1(X0_41,sK2) ),
% 0.77/1.05      inference(subtyping,[status(esa)],[c_170]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_401,plain,
% 0.77/1.05      ( r2_hidden(X0_42,k1_relat_1(k8_relat_1(X0_41,sK2))) = iProver_top
% 0.77/1.05      | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
% 0.77/1.05      | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) != iProver_top ),
% 0.77/1.05      inference(light_normalisation,[status(thm)],[c_369,c_224]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_412,plain,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,sK0),sK1) != iProver_top
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(sK2)) != iProver_top ),
% 0.77/1.05      inference(instantiation,[status(thm)],[c_401]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_4,negated_conjecture,
% 0.77/1.05      ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
% 0.77/1.05      | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
% 0.77/1.05      | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
% 0.77/1.05      inference(cnf_transformation,[],[f24]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_230,negated_conjecture,
% 0.77/1.05      ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
% 0.77/1.05      | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
% 0.77/1.05      | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
% 0.77/1.05      inference(subtyping,[status(esa)],[c_4]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_364,plain,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,sK0),sK1) != iProver_top
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) != iProver_top
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(sK2)) != iProver_top ),
% 0.77/1.05      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_3,plain,
% 0.77/1.05      ( r2_hidden(X0,k1_relat_1(X1))
% 0.77/1.05      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 0.77/1.05      | ~ v1_funct_1(X1)
% 0.77/1.05      | ~ v1_relat_1(X1) ),
% 0.77/1.05      inference(cnf_transformation,[],[f17]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_102,plain,
% 0.77/1.05      ( r2_hidden(X0,k1_relat_1(X1))
% 0.77/1.05      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 0.77/1.05      | ~ v1_relat_1(X1)
% 0.77/1.05      | sK2 != X1 ),
% 0.77/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_103,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
% 0.77/1.05      | r2_hidden(X0,k1_relat_1(sK2))
% 0.77/1.05      | ~ v1_relat_1(sK2) ),
% 0.77/1.05      inference(unflattening,[status(thm)],[c_102]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_107,plain,
% 0.77/1.05      ( r2_hidden(X0,k1_relat_1(sK2))
% 0.77/1.05      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ),
% 0.77/1.05      inference(global_propositional_subsumption,
% 0.77/1.05                [status(thm)],
% 0.77/1.05                [c_103,c_8]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_108,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
% 0.77/1.05      | r2_hidden(X0,k1_relat_1(sK2)) ),
% 0.77/1.05      inference(renaming,[status(thm)],[c_107]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_227,plain,
% 0.77/1.05      ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41))))
% 0.77/1.05      | r2_hidden(X0_42,k1_relat_1(sK2)) ),
% 0.77/1.05      inference(subtyping,[status(esa)],[c_108]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_367,plain,
% 0.77/1.05      ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41)))) != iProver_top
% 0.77/1.05      | r2_hidden(X0_42,k1_relat_1(sK2)) = iProver_top ),
% 0.77/1.05      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_380,plain,
% 0.77/1.05      ( r2_hidden(X0_42,k1_relat_1(k8_relat_1(X0_41,sK2))) != iProver_top
% 0.77/1.05      | r2_hidden(X0_42,k1_relat_1(sK2)) = iProver_top ),
% 0.77/1.05      inference(light_normalisation,[status(thm)],[c_367,c_224]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_2,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 0.77/1.05      | r2_hidden(k1_funct_1(X1,X0),X2)
% 0.77/1.05      | ~ v1_funct_1(X1)
% 0.77/1.05      | ~ v1_relat_1(X1) ),
% 0.77/1.05      inference(cnf_transformation,[],[f18]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_120,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 0.77/1.05      | r2_hidden(k1_funct_1(X1,X0),X2)
% 0.77/1.05      | ~ v1_relat_1(X1)
% 0.77/1.05      | sK2 != X1 ),
% 0.77/1.05      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_121,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
% 0.77/1.05      | r2_hidden(k1_funct_1(sK2,X0),X1)
% 0.77/1.05      | ~ v1_relat_1(sK2) ),
% 0.77/1.05      inference(unflattening,[status(thm)],[c_120]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_125,plain,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,X0),X1)
% 0.77/1.05      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1)))) ),
% 0.77/1.05      inference(global_propositional_subsumption,
% 0.77/1.05                [status(thm)],
% 0.77/1.05                [c_121,c_8]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_126,plain,
% 0.77/1.05      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X1))))
% 0.77/1.05      | r2_hidden(k1_funct_1(sK2,X0),X1) ),
% 0.77/1.05      inference(renaming,[status(thm)],[c_125]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_226,plain,
% 0.77/1.05      ( ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41))))
% 0.77/1.05      | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) ),
% 0.77/1.05      inference(subtyping,[status(esa)],[c_126]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_368,plain,
% 0.77/1.05      ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0_41)))) != iProver_top
% 0.77/1.05      | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) = iProver_top ),
% 0.77/1.05      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_388,plain,
% 0.77/1.05      ( r2_hidden(X0_42,k1_relat_1(k8_relat_1(X0_41,sK2))) != iProver_top
% 0.77/1.05      | r2_hidden(k1_funct_1(sK2,X0_42),X0_41) = iProver_top ),
% 0.77/1.05      inference(light_normalisation,[status(thm)],[c_368,c_224]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_5,negated_conjecture,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
% 0.77/1.05      inference(cnf_transformation,[],[f23]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_229,negated_conjecture,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
% 0.77/1.05      inference(subtyping,[status(esa)],[c_5]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_365,plain,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,sK0),sK1) = iProver_top
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top ),
% 0.77/1.05      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_392,plain,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,sK0),sK1) = iProver_top ),
% 0.77/1.05      inference(backward_subsumption_resolution,
% 0.77/1.05                [status(thm)],
% 0.77/1.05                [c_388,c_365]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_399,plain,
% 0.77/1.05      ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) != iProver_top ),
% 0.77/1.05      inference(forward_subsumption_resolution,
% 0.77/1.05                [status(thm)],
% 0.77/1.05                [c_364,c_380,c_392]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_12,plain,
% 0.77/1.05      ( r2_hidden(k1_funct_1(sK2,sK0),sK1) = iProver_top
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top ),
% 0.77/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_6,negated_conjecture,
% 0.77/1.05      ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(sK2)) ),
% 0.77/1.05      inference(cnf_transformation,[],[f22]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(c_11,plain,
% 0.77/1.05      ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) = iProver_top
% 0.77/1.05      | r2_hidden(sK0,k1_relat_1(sK2)) = iProver_top ),
% 0.77/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.77/1.05  
% 0.77/1.05  cnf(contradiction,plain,
% 0.77/1.05      ( $false ),
% 0.77/1.05      inference(minisat,[status(thm)],[c_412,c_399,c_12,c_11]) ).
% 0.77/1.05  
% 0.77/1.05  
% 0.77/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.77/1.05  
% 0.77/1.05  ------                               Statistics
% 0.77/1.05  
% 0.77/1.05  ------ General
% 0.77/1.05  
% 0.77/1.05  abstr_ref_over_cycles:                  0
% 0.77/1.05  abstr_ref_under_cycles:                 0
% 0.77/1.05  gc_basic_clause_elim:                   0
% 0.77/1.05  forced_gc_time:                         0
% 0.77/1.05  parsing_time:                           0.007
% 0.77/1.05  unif_index_cands_time:                  0.
% 0.77/1.05  unif_index_add_time:                    0.
% 0.77/1.05  orderings_time:                         0.
% 0.77/1.05  out_proof_time:                         0.009
% 0.77/1.05  total_time:                             0.052
% 0.77/1.05  num_of_symbols:                         43
% 0.77/1.05  num_of_terms:                           353
% 0.77/1.05  
% 0.77/1.05  ------ Preprocessing
% 0.77/1.05  
% 0.77/1.05  num_of_splits:                          0
% 0.77/1.05  num_of_split_atoms:                     0
% 0.77/1.05  num_of_reused_defs:                     0
% 0.77/1.05  num_eq_ax_congr_red:                    4
% 0.77/1.05  num_of_sem_filtered_clauses:            1
% 0.77/1.05  num_of_subtypes:                        4
% 0.77/1.05  monotx_restored_types:                  0
% 0.77/1.05  sat_num_of_epr_types:                   0
% 0.77/1.05  sat_num_of_non_cyclic_types:            0
% 0.77/1.05  sat_guarded_non_collapsed_types:        0
% 0.77/1.05  num_pure_diseq_elim:                    0
% 0.77/1.05  simp_replaced_by:                       0
% 0.77/1.05  res_preprocessed:                       51
% 0.77/1.05  prep_upred:                             0
% 0.77/1.05  prep_unflattend:                        4
% 0.77/1.05  smt_new_axioms:                         0
% 0.77/1.05  pred_elim_cands:                        1
% 0.77/1.05  pred_elim:                              2
% 0.77/1.05  pred_elim_cl:                           2
% 0.77/1.05  pred_elim_cycles:                       4
% 0.77/1.05  merged_defs:                            0
% 0.77/1.05  merged_defs_ncl:                        0
% 0.77/1.05  bin_hyper_res:                          0
% 0.77/1.05  prep_cycles:                            4
% 0.77/1.05  pred_elim_time:                         0.001
% 0.77/1.05  splitting_time:                         0.
% 0.77/1.05  sem_filter_time:                        0.
% 0.77/1.05  monotx_time:                            0.
% 0.77/1.05  subtype_inf_time:                       0.
% 0.77/1.05  
% 0.77/1.05  ------ Problem properties
% 0.77/1.05  
% 0.77/1.05  clauses:                                7
% 0.77/1.05  conjectures:                            3
% 0.77/1.05  epr:                                    0
% 0.77/1.05  horn:                                   5
% 0.77/1.05  ground:                                 3
% 0.77/1.05  unary:                                  1
% 0.77/1.05  binary:                                 4
% 0.77/1.05  lits:                                   15
% 0.77/1.05  lits_eq:                                1
% 0.77/1.05  fd_pure:                                0
% 0.77/1.05  fd_pseudo:                              0
% 0.77/1.05  fd_cond:                                0
% 0.77/1.05  fd_pseudo_cond:                         0
% 0.77/1.05  ac_symbols:                             0
% 0.77/1.05  
% 0.77/1.05  ------ Propositional Solver
% 0.77/1.05  
% 0.77/1.05  prop_solver_calls:                      21
% 0.77/1.05  prop_fast_solver_calls:                 246
% 0.77/1.05  smt_solver_calls:                       0
% 0.77/1.05  smt_fast_solver_calls:                  0
% 0.77/1.05  prop_num_of_clauses:                    94
% 0.77/1.05  prop_preprocess_simplified:             959
% 0.77/1.05  prop_fo_subsumed:                       3
% 0.77/1.05  prop_solver_time:                       0.
% 0.77/1.05  smt_solver_time:                        0.
% 0.77/1.05  smt_fast_solver_time:                   0.
% 0.77/1.05  prop_fast_solver_time:                  0.
% 0.77/1.05  prop_unsat_core_time:                   0.
% 0.77/1.05  
% 0.77/1.05  ------ QBF
% 0.77/1.05  
% 0.77/1.05  qbf_q_res:                              0
% 0.77/1.05  qbf_num_tautologies:                    0
% 0.77/1.05  qbf_prep_cycles:                        0
% 0.77/1.05  
% 0.77/1.05  ------ BMC1
% 0.77/1.05  
% 0.77/1.05  bmc1_current_bound:                     -1
% 0.77/1.05  bmc1_last_solved_bound:                 -1
% 0.77/1.05  bmc1_unsat_core_size:                   -1
% 0.77/1.05  bmc1_unsat_core_parents_size:           -1
% 0.77/1.05  bmc1_merge_next_fun:                    0
% 0.77/1.05  bmc1_unsat_core_clauses_time:           0.
% 0.77/1.05  
% 0.77/1.05  ------ Instantiation
% 0.77/1.05  
% 0.77/1.05  inst_num_of_clauses:                    17
% 0.77/1.05  inst_num_in_passive:                    0
% 0.77/1.05  inst_num_in_active:                     0
% 0.77/1.05  inst_num_in_unprocessed:                17
% 0.77/1.05  inst_num_of_loops:                      0
% 0.77/1.05  inst_num_of_learning_restarts:          0
% 0.77/1.05  inst_num_moves_active_passive:          0
% 0.77/1.05  inst_lit_activity:                      0
% 0.77/1.05  inst_lit_activity_moves:                0
% 0.77/1.05  inst_num_tautologies:                   0
% 0.77/1.05  inst_num_prop_implied:                  0
% 0.77/1.05  inst_num_existing_simplified:           0
% 0.77/1.05  inst_num_eq_res_simplified:             0
% 0.77/1.05  inst_num_child_elim:                    0
% 0.77/1.05  inst_num_of_dismatching_blockings:      0
% 0.77/1.05  inst_num_of_non_proper_insts:           0
% 0.77/1.05  inst_num_of_duplicates:                 0
% 0.77/1.05  inst_inst_num_from_inst_to_res:         0
% 0.77/1.05  inst_dismatching_checking_time:         0.
% 0.77/1.05  
% 0.77/1.05  ------ Resolution
% 0.77/1.05  
% 0.77/1.05  res_num_of_clauses:                     0
% 0.77/1.05  res_num_in_passive:                     0
% 0.77/1.05  res_num_in_active:                      0
% 0.77/1.05  res_num_of_loops:                       55
% 0.77/1.05  res_forward_subset_subsumed:            0
% 0.77/1.05  res_backward_subset_subsumed:           0
% 0.77/1.05  res_forward_subsumed:                   0
% 0.77/1.05  res_backward_subsumed:                  0
% 0.77/1.05  res_forward_subsumption_resolution:     0
% 0.77/1.05  res_backward_subsumption_resolution:    0
% 0.77/1.05  res_clause_to_clause_subsumption:       14
% 0.77/1.05  res_orphan_elimination:                 0
% 0.77/1.05  res_tautology_del:                      0
% 0.77/1.05  res_num_eq_res_simplified:              0
% 0.77/1.05  res_num_sel_changes:                    0
% 0.77/1.05  res_moves_from_active_to_pass:          0
% 0.77/1.05  
% 0.77/1.05  ------ Superposition
% 0.77/1.05  
% 0.77/1.05  sup_time_total:                         0.
% 0.77/1.05  sup_time_generating:                    0.
% 0.77/1.05  sup_time_sim_full:                      0.
% 0.77/1.05  sup_time_sim_immed:                     0.
% 0.77/1.05  
% 0.77/1.05  sup_num_of_clauses:                     5
% 0.77/1.05  sup_num_in_active:                      0
% 0.77/1.05  sup_num_in_passive:                     5
% 0.77/1.05  sup_num_of_loops:                       0
% 0.77/1.05  sup_fw_superposition:                   0
% 0.77/1.05  sup_bw_superposition:                   0
% 0.77/1.05  sup_immediate_simplified:               0
% 0.77/1.05  sup_given_eliminated:                   0
% 0.77/1.05  comparisons_done:                       0
% 0.77/1.05  comparisons_avoided:                    0
% 0.77/1.05  
% 0.77/1.05  ------ Simplifications
% 0.77/1.05  
% 0.77/1.05  
% 0.77/1.05  sim_fw_subset_subsumed:                 0
% 0.77/1.05  sim_bw_subset_subsumed:                 0
% 0.77/1.05  sim_fw_subsumed:                        0
% 0.77/1.05  sim_bw_subsumed:                        0
% 0.77/1.05  sim_fw_subsumption_res:                 2
% 0.77/1.05  sim_bw_subsumption_res:                 2
% 0.77/1.05  sim_tautology_del:                      0
% 0.77/1.05  sim_eq_tautology_del:                   0
% 0.77/1.05  sim_eq_res_simp:                        0
% 0.77/1.05  sim_fw_demodulated:                     0
% 0.77/1.05  sim_bw_demodulated:                     0
% 0.77/1.05  sim_light_normalised:                   3
% 0.77/1.05  sim_joinable_taut:                      0
% 0.77/1.05  sim_joinable_simp:                      0
% 0.77/1.05  sim_ac_normalised:                      0
% 0.77/1.05  sim_smt_subsumption:                    0
% 0.77/1.05  
%------------------------------------------------------------------------------
