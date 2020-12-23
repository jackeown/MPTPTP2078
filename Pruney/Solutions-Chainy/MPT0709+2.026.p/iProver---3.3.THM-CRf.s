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
% DateTime   : Thu Dec  3 11:52:39 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 218 expanded)
%              Number of clauses        :   50 (  69 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  251 ( 846 expanded)
%              Number of equality atoms :   61 ( 182 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f37])).

fof(f58,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_396,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1078,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
    | k9_relat_1(sK1,sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_2561,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
    | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_6604,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k9_relat_1(sK1,sK0)
    | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_623,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_628,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK1))
    | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_18])).

cnf(c_621,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_1021,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_628,c_621])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_275,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_276,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_1023,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1021,c_276])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_243,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_620,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_1267,plain,
    ( r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1023,c_620])).

cnf(c_1569,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k9_relat_1(sK1,X0)
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_621])).

cnf(c_2885,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_623,c_1569])).

cnf(c_394,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1306,plain,
    ( k9_relat_1(sK1,sK0) = k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_1158,plain,
    ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,X0))
    | ~ r1_tarski(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_1230,plain,
    ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_896,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_280,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_281,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_861,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_200,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_201,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_203,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_201,c_18,c_17])).

cnf(c_789,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_756,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_254,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_255,plain,
    ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_707,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_14,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6604,c_2885,c_1306,c_1230,c_896,c_861,c_789,c_756,c_707,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:10:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.52/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.99  
% 3.52/0.99  ------  iProver source info
% 3.52/0.99  
% 3.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.99  git: non_committed_changes: false
% 3.52/0.99  git: last_make_outside_of_git: false
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    --mode clausify
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         false
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     num_symb
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       true
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     false
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   []
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_full_bw                           [BwDemod]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  ------ Parsing...
% 3.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  ------ Proving...
% 3.52/0.99  ------ Problem Properties 
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  clauses                                 15
% 3.52/0.99  conjectures                             2
% 3.52/0.99  EPR                                     3
% 3.52/0.99  Horn                                    15
% 3.52/0.99  unary                                   7
% 3.52/0.99  binary                                  5
% 3.52/0.99  lits                                    26
% 3.52/0.99  lits eq                                 5
% 3.52/0.99  fd_pure                                 0
% 3.52/0.99  fd_pseudo                               0
% 3.52/0.99  fd_cond                                 0
% 3.52/0.99  fd_pseudo_cond                          1
% 3.52/0.99  AC symbols                              0
% 3.52/0.99  
% 3.52/0.99  ------ Schedule dynamic 5 is on 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  Current options:
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    --mode clausify
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         false
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     none
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       false
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     false
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   []
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_full_bw                           [BwDemod]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS status Theorem for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  fof(f16,conjecture,(
% 3.52/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f17,negated_conjecture,(
% 3.52/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.52/0.99    inference(negated_conjecture,[],[f16])).
% 3.52/0.99  
% 3.52/0.99  fof(f33,plain,(
% 3.52/0.99    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.52/0.99    inference(ennf_transformation,[],[f17])).
% 3.52/0.99  
% 3.52/0.99  fof(f34,plain,(
% 3.52/0.99    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.52/0.99    inference(flattening,[],[f33])).
% 3.52/0.99  
% 3.52/0.99  fof(f37,plain,(
% 3.52/0.99    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f38,plain,(
% 3.52/0.99    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f37])).
% 3.52/0.99  
% 3.52/0.99  fof(f58,plain,(
% 3.52/0.99    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.52/0.99    inference(cnf_transformation,[],[f38])).
% 3.52/0.99  
% 3.52/0.99  fof(f1,axiom,(
% 3.52/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f35,plain,(
% 3.52/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.99    inference(nnf_transformation,[],[f1])).
% 3.52/0.99  
% 3.52/0.99  fof(f36,plain,(
% 3.52/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.99    inference(flattening,[],[f35])).
% 3.52/0.99  
% 3.52/0.99  fof(f40,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.52/0.99    inference(cnf_transformation,[],[f36])).
% 3.52/0.99  
% 3.52/0.99  fof(f64,plain,(
% 3.52/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.52/0.99    inference(equality_resolution,[],[f40])).
% 3.52/0.99  
% 3.52/0.99  fof(f14,axiom,(
% 3.52/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f29,plain,(
% 3.52/0.99    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.52/0.99    inference(ennf_transformation,[],[f14])).
% 3.52/0.99  
% 3.52/0.99  fof(f30,plain,(
% 3.52/0.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(flattening,[],[f29])).
% 3.52/0.99  
% 3.52/0.99  fof(f54,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f57,plain,(
% 3.52/0.99    v1_funct_1(sK1)),
% 3.52/0.99    inference(cnf_transformation,[],[f38])).
% 3.52/0.99  
% 3.52/0.99  fof(f56,plain,(
% 3.52/0.99    v1_relat_1(sK1)),
% 3.52/0.99    inference(cnf_transformation,[],[f38])).
% 3.52/0.99  
% 3.52/0.99  fof(f11,axiom,(
% 3.52/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f25,plain,(
% 3.52/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(ennf_transformation,[],[f11])).
% 3.52/0.99  
% 3.52/0.99  fof(f51,plain,(
% 3.52/0.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f25])).
% 3.52/0.99  
% 3.52/0.99  fof(f9,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f22,plain,(
% 3.52/0.99    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.52/0.99    inference(ennf_transformation,[],[f9])).
% 3.52/0.99  
% 3.52/0.99  fof(f23,plain,(
% 3.52/0.99    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.52/0.99    inference(flattening,[],[f22])).
% 3.52/0.99  
% 3.52/0.99  fof(f49,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f23])).
% 3.52/0.99  
% 3.52/0.99  fof(f10,axiom,(
% 3.52/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f24,plain,(
% 3.52/0.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f10])).
% 3.52/0.99  
% 3.52/0.99  fof(f50,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f24])).
% 3.52/0.99  
% 3.52/0.99  fof(f15,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f31,plain,(
% 3.52/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.52/0.99    inference(ennf_transformation,[],[f15])).
% 3.52/0.99  
% 3.52/0.99  fof(f32,plain,(
% 3.52/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.52/0.99    inference(flattening,[],[f31])).
% 3.52/0.99  
% 3.52/0.99  fof(f55,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f59,plain,(
% 3.52/0.99    v2_funct_1(sK1)),
% 3.52/0.99    inference(cnf_transformation,[],[f38])).
% 3.52/0.99  
% 3.52/0.99  fof(f41,plain,(
% 3.52/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f36])).
% 3.52/0.99  
% 3.52/0.99  fof(f13,axiom,(
% 3.52/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f27,plain,(
% 3.52/0.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f13])).
% 3.52/0.99  
% 3.52/0.99  fof(f28,plain,(
% 3.52/0.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(flattening,[],[f27])).
% 3.52/0.99  
% 3.52/0.99  fof(f53,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f28])).
% 3.52/0.99  
% 3.52/0.99  fof(f60,plain,(
% 3.52/0.99    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 3.52/0.99    inference(cnf_transformation,[],[f38])).
% 3.52/0.99  
% 3.52/0.99  cnf(c_396,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/0.99      theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1078,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1)
% 3.52/0.99      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 3.52/0.99      | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
% 3.52/0.99      | k9_relat_1(sK1,sK0) != X1 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_396]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2561,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
% 3.52/0.99      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 3.52/0.99      | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
% 3.52/0.99      | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1078]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_6604,plain,
% 3.52/0.99      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 3.52/0.99      | ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
% 3.52/0.99      | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k9_relat_1(sK1,sK0)
% 3.52/0.99      | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_2561]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_16,negated_conjecture,
% 3.52/0.99      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_623,plain,
% 3.52/0.99      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1,plain,
% 3.52/0.99      ( r1_tarski(X0,X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_628,plain,
% 3.52/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.52/0.99      | ~ v1_funct_1(X1)
% 3.52/0.99      | ~ v1_relat_1(X1)
% 3.52/0.99      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_17,negated_conjecture,
% 3.52/0.99      ( v1_funct_1(sK1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_221,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.52/0.99      | ~ v1_relat_1(X1)
% 3.52/0.99      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 3.52/0.99      | sK1 != X1 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_222,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,k2_relat_1(sK1))
% 3.52/0.99      | ~ v1_relat_1(sK1)
% 3.52/0.99      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_221]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_18,negated_conjecture,
% 3.52/0.99      ( v1_relat_1(sK1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_226,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,k2_relat_1(sK1))
% 3.52/0.99      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_222,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_621,plain,
% 3.52/0.99      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0
% 3.52/0.99      | r1_tarski(X0,k2_relat_1(sK1)) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1021,plain,
% 3.52/0.99      ( k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) = k2_relat_1(sK1) ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_628,c_621]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_9,plain,
% 3.52/0.99      ( ~ v1_relat_1(X0)
% 3.52/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_275,plain,
% 3.52/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | sK1 != X0 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_276,plain,
% 3.52/0.99      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_275]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1023,plain,
% 3.52/0.99      ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_1021,c_276]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_7,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1)
% 3.52/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.52/0.99      | ~ v1_relat_1(X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_242,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1)
% 3.52/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.52/0.99      | sK1 != X2 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_243,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1)
% 3.52/0.99      | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_242]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_620,plain,
% 3.52/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.52/0.99      | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1267,plain,
% 3.52/0.99      ( r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
% 3.52/0.99      | r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1)) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_1023,c_620]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1569,plain,
% 3.52/0.99      ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k9_relat_1(sK1,X0)
% 3.52/0.99      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_1267,c_621]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2885,plain,
% 3.52/0.99      ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,sK0) ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_623,c_1569]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_394,plain,( X0 = X0 ),theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1306,plain,
% 3.52/0.99      ( k9_relat_1(sK1,sK0) = k9_relat_1(sK1,sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_394]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1158,plain,
% 3.52/0.99      ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,X0))
% 3.52/0.99      | ~ r1_tarski(sK0,X0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_243]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1230,plain,
% 3.52/0.99      ( r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
% 3.52/0.99      | ~ r1_tarski(sK0,sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1158]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_896,plain,
% 3.52/0.99      ( r1_tarski(sK0,sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_8,plain,
% 3.52/0.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_280,plain,
% 3.52/0.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | sK1 != X0 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_281,plain,
% 3.52/0.99      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_861,plain,
% 3.52/0.99      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_281]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_13,plain,
% 3.52/0.99      ( r1_tarski(X0,X1)
% 3.52/0.99      | ~ r1_tarski(X0,k1_relat_1(X2))
% 3.52/0.99      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.52/0.99      | ~ v2_funct_1(X2)
% 3.52/0.99      | ~ v1_funct_1(X2)
% 3.52/0.99      | ~ v1_relat_1(X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_15,negated_conjecture,
% 3.52/0.99      ( v2_funct_1(sK1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_200,plain,
% 3.52/0.99      ( r1_tarski(X0,X1)
% 3.52/0.99      | ~ r1_tarski(X0,k1_relat_1(X2))
% 3.52/0.99      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.52/0.99      | ~ v1_funct_1(X2)
% 3.52/0.99      | ~ v1_relat_1(X2)
% 3.52/0.99      | sK1 != X2 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_201,plain,
% 3.52/0.99      ( r1_tarski(X0,X1)
% 3.52/0.99      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 3.52/0.99      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
% 3.52/0.99      | ~ v1_funct_1(sK1)
% 3.52/0.99      | ~ v1_relat_1(sK1) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_200]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_203,plain,
% 3.52/0.99      ( r1_tarski(X0,X1)
% 3.52/0.99      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 3.52/0.99      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_201,c_18,c_17]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_789,plain,
% 3.52/0.99      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
% 3.52/0.99      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 3.52/0.99      | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_203]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_0,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.52/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_756,plain,
% 3.52/0.99      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 3.52/0.99      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 3.52/0.99      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_11,plain,
% 3.52/0.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 3.52/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.52/0.99      | ~ v1_relat_1(X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_254,plain,
% 3.52/0.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 3.52/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.52/0.99      | sK1 != X1 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_255,plain,
% 3.52/0.99      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
% 3.52/0.99      | ~ r1_tarski(X0,k1_relat_1(sK1)) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_254]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_707,plain,
% 3.52/0.99      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 3.52/0.99      | ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_255]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_14,negated_conjecture,
% 3.52/0.99      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(contradiction,plain,
% 3.52/0.99      ( $false ),
% 3.52/0.99      inference(minisat,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_6604,c_2885,c_1306,c_1230,c_896,c_861,c_789,c_756,
% 3.52/0.99                 c_707,c_14,c_16]) ).
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  ------                               Statistics
% 3.52/0.99  
% 3.52/0.99  ------ General
% 3.52/0.99  
% 3.52/0.99  abstr_ref_over_cycles:                  0
% 3.52/0.99  abstr_ref_under_cycles:                 0
% 3.52/0.99  gc_basic_clause_elim:                   0
% 3.52/0.99  forced_gc_time:                         0
% 3.52/0.99  parsing_time:                           0.009
% 3.52/0.99  unif_index_cands_time:                  0.
% 3.52/0.99  unif_index_add_time:                    0.
% 3.52/0.99  orderings_time:                         0.
% 3.52/0.99  out_proof_time:                         0.008
% 3.52/0.99  total_time:                             0.219
% 3.52/0.99  num_of_symbols:                         45
% 3.52/0.99  num_of_terms:                           6860
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing
% 3.52/0.99  
% 3.52/0.99  num_of_splits:                          0
% 3.52/0.99  num_of_split_atoms:                     0
% 3.52/0.99  num_of_reused_defs:                     0
% 3.52/0.99  num_eq_ax_congr_red:                    19
% 3.52/0.99  num_of_sem_filtered_clauses:            1
% 3.52/0.99  num_of_subtypes:                        0
% 3.52/0.99  monotx_restored_types:                  0
% 3.52/0.99  sat_num_of_epr_types:                   0
% 3.52/0.99  sat_num_of_non_cyclic_types:            0
% 3.52/0.99  sat_guarded_non_collapsed_types:        0
% 3.52/0.99  num_pure_diseq_elim:                    0
% 3.52/0.99  simp_replaced_by:                       0
% 3.52/0.99  res_preprocessed:                       82
% 3.52/0.99  prep_upred:                             0
% 3.52/0.99  prep_unflattend:                        7
% 3.52/0.99  smt_new_axioms:                         0
% 3.52/0.99  pred_elim_cands:                        1
% 3.52/0.99  pred_elim:                              3
% 3.52/0.99  pred_elim_cl:                           3
% 3.52/0.99  pred_elim_cycles:                       5
% 3.52/0.99  merged_defs:                            0
% 3.52/0.99  merged_defs_ncl:                        0
% 3.52/0.99  bin_hyper_res:                          0
% 3.52/0.99  prep_cycles:                            4
% 3.52/0.99  pred_elim_time:                         0.002
% 3.52/0.99  splitting_time:                         0.
% 3.52/0.99  sem_filter_time:                        0.
% 3.52/0.99  monotx_time:                            0.001
% 3.52/0.99  subtype_inf_time:                       0.
% 3.52/0.99  
% 3.52/0.99  ------ Problem properties
% 3.52/0.99  
% 3.52/0.99  clauses:                                15
% 3.52/0.99  conjectures:                            2
% 3.52/0.99  epr:                                    3
% 3.52/0.99  horn:                                   15
% 3.52/0.99  ground:                                 3
% 3.52/0.99  unary:                                  7
% 3.52/0.99  binary:                                 5
% 3.52/0.99  lits:                                   26
% 3.52/0.99  lits_eq:                                5
% 3.52/0.99  fd_pure:                                0
% 3.52/0.99  fd_pseudo:                              0
% 3.52/0.99  fd_cond:                                0
% 3.52/0.99  fd_pseudo_cond:                         1
% 3.52/0.99  ac_symbols:                             0
% 3.52/0.99  
% 3.52/0.99  ------ Propositional Solver
% 3.52/0.99  
% 3.52/0.99  prop_solver_calls:                      28
% 3.52/0.99  prop_fast_solver_calls:                 462
% 3.52/0.99  smt_solver_calls:                       0
% 3.52/0.99  smt_fast_solver_calls:                  0
% 3.52/0.99  prop_num_of_clauses:                    2860
% 3.52/0.99  prop_preprocess_simplified:             5976
% 3.52/0.99  prop_fo_subsumed:                       7
% 3.52/0.99  prop_solver_time:                       0.
% 3.52/0.99  smt_solver_time:                        0.
% 3.52/0.99  smt_fast_solver_time:                   0.
% 3.52/0.99  prop_fast_solver_time:                  0.
% 3.52/0.99  prop_unsat_core_time:                   0.
% 3.52/0.99  
% 3.52/0.99  ------ QBF
% 3.52/0.99  
% 3.52/0.99  qbf_q_res:                              0
% 3.52/0.99  qbf_num_tautologies:                    0
% 3.52/0.99  qbf_prep_cycles:                        0
% 3.52/0.99  
% 3.52/0.99  ------ BMC1
% 3.52/0.99  
% 3.52/0.99  bmc1_current_bound:                     -1
% 3.52/0.99  bmc1_last_solved_bound:                 -1
% 3.52/0.99  bmc1_unsat_core_size:                   -1
% 3.52/0.99  bmc1_unsat_core_parents_size:           -1
% 3.52/0.99  bmc1_merge_next_fun:                    0
% 3.52/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation
% 3.52/0.99  
% 3.52/0.99  inst_num_of_clauses:                    714
% 3.52/0.99  inst_num_in_passive:                    115
% 3.52/0.99  inst_num_in_active:                     315
% 3.52/0.99  inst_num_in_unprocessed:                284
% 3.52/0.99  inst_num_of_loops:                      322
% 3.52/0.99  inst_num_of_learning_restarts:          0
% 3.52/0.99  inst_num_moves_active_passive:          3
% 3.52/0.99  inst_lit_activity:                      0
% 3.52/0.99  inst_lit_activity_moves:                0
% 3.52/0.99  inst_num_tautologies:                   0
% 3.52/0.99  inst_num_prop_implied:                  0
% 3.52/0.99  inst_num_existing_simplified:           0
% 3.52/0.99  inst_num_eq_res_simplified:             0
% 3.52/0.99  inst_num_child_elim:                    0
% 3.52/0.99  inst_num_of_dismatching_blockings:      256
% 3.52/0.99  inst_num_of_non_proper_insts:           1003
% 3.52/0.99  inst_num_of_duplicates:                 0
% 3.52/0.99  inst_inst_num_from_inst_to_res:         0
% 3.52/0.99  inst_dismatching_checking_time:         0.
% 3.52/0.99  
% 3.52/0.99  ------ Resolution
% 3.52/0.99  
% 3.52/0.99  res_num_of_clauses:                     0
% 3.52/0.99  res_num_in_passive:                     0
% 3.52/0.99  res_num_in_active:                      0
% 3.52/0.99  res_num_of_loops:                       86
% 3.52/0.99  res_forward_subset_subsumed:            91
% 3.52/0.99  res_backward_subset_subsumed:           6
% 3.52/0.99  res_forward_subsumed:                   0
% 3.52/0.99  res_backward_subsumed:                  0
% 3.52/0.99  res_forward_subsumption_resolution:     0
% 3.52/0.99  res_backward_subsumption_resolution:    0
% 3.52/0.99  res_clause_to_clause_subsumption:       1001
% 3.52/0.99  res_orphan_elimination:                 0
% 3.52/0.99  res_tautology_del:                      91
% 3.52/0.99  res_num_eq_res_simplified:              0
% 3.52/0.99  res_num_sel_changes:                    0
% 3.52/0.99  res_moves_from_active_to_pass:          0
% 3.52/0.99  
% 3.52/0.99  ------ Superposition
% 3.52/0.99  
% 3.52/0.99  sup_time_total:                         0.
% 3.52/0.99  sup_time_generating:                    0.
% 3.52/0.99  sup_time_sim_full:                      0.
% 3.52/0.99  sup_time_sim_immed:                     0.
% 3.52/0.99  
% 3.52/0.99  sup_num_of_clauses:                     187
% 3.52/0.99  sup_num_in_active:                      64
% 3.52/0.99  sup_num_in_passive:                     123
% 3.52/0.99  sup_num_of_loops:                       64
% 3.52/0.99  sup_fw_superposition:                   232
% 3.52/0.99  sup_bw_superposition:                   105
% 3.52/0.99  sup_immediate_simplified:               106
% 3.52/0.99  sup_given_eliminated:                   0
% 3.52/0.99  comparisons_done:                       0
% 3.52/0.99  comparisons_avoided:                    0
% 3.52/0.99  
% 3.52/0.99  ------ Simplifications
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  sim_fw_subset_subsumed:                 7
% 3.52/0.99  sim_bw_subset_subsumed:                 4
% 3.52/0.99  sim_fw_subsumed:                        49
% 3.52/0.99  sim_bw_subsumed:                        2
% 3.52/0.99  sim_fw_subsumption_res:                 0
% 3.52/0.99  sim_bw_subsumption_res:                 0
% 3.52/0.99  sim_tautology_del:                      18
% 3.52/0.99  sim_eq_tautology_del:                   17
% 3.52/0.99  sim_eq_res_simp:                        0
% 3.52/0.99  sim_fw_demodulated:                     8
% 3.52/0.99  sim_bw_demodulated:                     0
% 3.52/0.99  sim_light_normalised:                   63
% 3.52/0.99  sim_joinable_taut:                      0
% 3.52/0.99  sim_joinable_simp:                      0
% 3.52/0.99  sim_ac_normalised:                      0
% 3.52/0.99  sim_smt_subsumption:                    0
% 3.52/0.99  
%------------------------------------------------------------------------------
