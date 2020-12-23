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
% DateTime   : Thu Dec  3 11:52:36 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 148 expanded)
%              Number of clauses        :   43 (  48 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 ( 524 expanded)
%              Number of equality atoms :   65 ( 131 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f42,f44,f44])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,k6_subset_1(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f51,f58])).

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

fof(f30,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f34,plain,
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

fof(f35,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f34])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( r1_tarski(k6_subset_1(X0,k6_subset_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6896,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),X0)),k9_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_27944,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))),k9_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6896])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_218,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_219,plain,
    ( ~ v1_relat_1(sK1)
    | k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_223,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_219,c_19])).

cnf(c_27940,plain,
    ( k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_342,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_628,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3))
    | k9_relat_1(sK1,X2) != X0
    | k9_relat_1(sK1,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_914,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
    | k9_relat_1(sK1,sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1292,plain,
    ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
    | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_11864,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | ~ r1_tarski(k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))),k9_relat_1(sK1,sK0))
    | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))))
    | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_341,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1405,plain,
    ( X0 != X1
    | k9_relat_1(sK1,X2) != X1
    | k9_relat_1(sK1,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_3310,plain,
    ( X0 != k9_relat_1(sK1,X1)
    | k9_relat_1(sK1,X1) = X0
    | k9_relat_1(sK1,X1) != k9_relat_1(sK1,X1) ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_10116,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) != k9_relat_1(sK1,k10_relat_1(sK1,X0))
    | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1))))
    | k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) != k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_3310])).

cnf(c_11862,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))))
    | k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))) != k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_10116])).

cnf(c_340,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1399,plain,
    ( k9_relat_1(sK1,X0) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_3086,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_1293,plain,
    ( k9_relat_1(sK1,sK0) = k9_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_239,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_240,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_712,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_185,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_186,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_188,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_186,c_19,c_18])).

cnf(c_686,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_606,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_12,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_253,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_254,plain,
    ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_549,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_15,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27944,c_27940,c_11864,c_11862,c_3086,c_1293,c_712,c_686,c_606,c_549,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n007.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:11:36 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.92/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.92/1.49  
% 7.92/1.49  ------  iProver source info
% 7.92/1.49  
% 7.92/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.92/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.92/1.49  git: non_committed_changes: false
% 7.92/1.49  git: last_make_outside_of_git: false
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  ------ Parsing...
% 7.92/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.92/1.49  ------ Proving...
% 7.92/1.49  ------ Problem Properties 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  clauses                                 16
% 7.92/1.49  conjectures                             2
% 7.92/1.49  EPR                                     3
% 7.92/1.49  Horn                                    16
% 7.92/1.49  unary                                   12
% 7.92/1.49  binary                                  2
% 7.92/1.49  lits                                    22
% 7.92/1.49  lits eq                                 9
% 7.92/1.49  fd_pure                                 0
% 7.92/1.49  fd_pseudo                               0
% 7.92/1.49  fd_cond                                 1
% 7.92/1.49  fd_pseudo_cond                          1
% 7.92/1.49  AC symbols                              0
% 7.92/1.49  
% 7.92/1.49  ------ Input Options Time Limit: Unbounded
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  Current options:
% 7.92/1.49  ------ 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ Proving...
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS status Theorem for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  fof(f2,axiom,(
% 7.92/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f39,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f2])).
% 7.92/1.49  
% 7.92/1.49  fof(f5,axiom,(
% 7.92/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f42,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f5])).
% 7.92/1.49  
% 7.92/1.49  fof(f7,axiom,(
% 7.92/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f44,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f7])).
% 7.92/1.49  
% 7.92/1.49  fof(f58,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 7.92/1.49    inference(definition_unfolding,[],[f42,f44,f44])).
% 7.92/1.49  
% 7.92/1.49  fof(f59,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,k6_subset_1(X0,X1)),X0)) )),
% 7.92/1.49    inference(definition_unfolding,[],[f39,f58])).
% 7.92/1.49  
% 7.92/1.49  fof(f14,axiom,(
% 7.92/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f26,plain,(
% 7.92/1.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.92/1.49    inference(ennf_transformation,[],[f14])).
% 7.92/1.49  
% 7.92/1.49  fof(f27,plain,(
% 7.92/1.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.92/1.49    inference(flattening,[],[f26])).
% 7.92/1.49  
% 7.92/1.49  fof(f51,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f27])).
% 7.92/1.49  
% 7.92/1.49  fof(f62,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.92/1.49    inference(definition_unfolding,[],[f51,f58])).
% 7.92/1.49  
% 7.92/1.49  fof(f16,conjecture,(
% 7.92/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f17,negated_conjecture,(
% 7.92/1.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 7.92/1.49    inference(negated_conjecture,[],[f16])).
% 7.92/1.49  
% 7.92/1.49  fof(f30,plain,(
% 7.92/1.49    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.92/1.49    inference(ennf_transformation,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  fof(f31,plain,(
% 7.92/1.49    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.92/1.49    inference(flattening,[],[f30])).
% 7.92/1.49  
% 7.92/1.49  fof(f34,plain,(
% 7.92/1.49    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f35,plain,(
% 7.92/1.49    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f34])).
% 7.92/1.49  
% 7.92/1.49  fof(f54,plain,(
% 7.92/1.49    v1_funct_1(sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f35])).
% 7.92/1.49  
% 7.92/1.49  fof(f53,plain,(
% 7.92/1.49    v1_relat_1(sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f35])).
% 7.92/1.49  
% 7.92/1.49  fof(f10,axiom,(
% 7.92/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f20,plain,(
% 7.92/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.92/1.49    inference(ennf_transformation,[],[f10])).
% 7.92/1.49  
% 7.92/1.49  fof(f47,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f20])).
% 7.92/1.49  
% 7.92/1.49  fof(f15,axiom,(
% 7.92/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f28,plain,(
% 7.92/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.92/1.49    inference(ennf_transformation,[],[f15])).
% 7.92/1.49  
% 7.92/1.49  fof(f29,plain,(
% 7.92/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.92/1.49    inference(flattening,[],[f28])).
% 7.92/1.49  
% 7.92/1.49  fof(f52,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f29])).
% 7.92/1.49  
% 7.92/1.49  fof(f56,plain,(
% 7.92/1.49    v2_funct_1(sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f35])).
% 7.92/1.49  
% 7.92/1.49  fof(f1,axiom,(
% 7.92/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f32,plain,(
% 7.92/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.92/1.49    inference(nnf_transformation,[],[f1])).
% 7.92/1.49  
% 7.92/1.49  fof(f33,plain,(
% 7.92/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.92/1.49    inference(flattening,[],[f32])).
% 7.92/1.49  
% 7.92/1.49  fof(f38,plain,(
% 7.92/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f33])).
% 7.92/1.49  
% 7.92/1.49  fof(f13,axiom,(
% 7.92/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f24,plain,(
% 7.92/1.49    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.92/1.49    inference(ennf_transformation,[],[f13])).
% 7.92/1.49  
% 7.92/1.49  fof(f25,plain,(
% 7.92/1.49    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.92/1.49    inference(flattening,[],[f24])).
% 7.92/1.49  
% 7.92/1.49  fof(f50,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f57,plain,(
% 7.92/1.49    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 7.92/1.49    inference(cnf_transformation,[],[f35])).
% 7.92/1.49  
% 7.92/1.49  fof(f55,plain,(
% 7.92/1.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 7.92/1.49    inference(cnf_transformation,[],[f35])).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3,plain,
% 7.92/1.49      ( r1_tarski(k6_subset_1(X0,k6_subset_1(X0,X1)),X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_6896,plain,
% 7.92/1.49      ( r1_tarski(k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),X0)),k9_relat_1(sK1,sK0)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_27944,plain,
% 7.92/1.49      ( r1_tarski(k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))),k9_relat_1(sK1,sK0)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_6896]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_13,plain,
% 7.92/1.49      ( ~ v1_funct_1(X0)
% 7.92/1.49      | ~ v1_relat_1(X0)
% 7.92/1.49      | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18,negated_conjecture,
% 7.92/1.49      ( v1_funct_1(sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_218,plain,
% 7.92/1.49      ( ~ v1_relat_1(X0)
% 7.92/1.49      | k6_subset_1(X1,k6_subset_1(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 7.92/1.49      | sK1 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_219,plain,
% 7.92/1.49      ( ~ v1_relat_1(sK1)
% 7.92/1.49      | k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_218]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19,negated_conjecture,
% 7.92/1.49      ( v1_relat_1(sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_223,plain,
% 7.92/1.49      ( k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_219,c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_27940,plain,
% 7.92/1.49      ( k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_223]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_342,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.92/1.49      theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_628,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1)
% 7.92/1.49      | r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3))
% 7.92/1.49      | k9_relat_1(sK1,X2) != X0
% 7.92/1.49      | k9_relat_1(sK1,X3) != X1 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_342]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_914,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1)
% 7.92/1.49      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 7.92/1.49      | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
% 7.92/1.49      | k9_relat_1(sK1,sK0) != X1 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_628]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1292,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
% 7.92/1.49      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 7.92/1.49      | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != X0
% 7.92/1.49      | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_914]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_11864,plain,
% 7.92/1.49      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 7.92/1.49      | ~ r1_tarski(k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))),k9_relat_1(sK1,sK0))
% 7.92/1.49      | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))))
% 7.92/1.49      | k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1292]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_341,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1405,plain,
% 7.92/1.49      ( X0 != X1 | k9_relat_1(sK1,X2) != X1 | k9_relat_1(sK1,X2) = X0 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_341]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3310,plain,
% 7.92/1.49      ( X0 != k9_relat_1(sK1,X1)
% 7.92/1.49      | k9_relat_1(sK1,X1) = X0
% 7.92/1.49      | k9_relat_1(sK1,X1) != k9_relat_1(sK1,X1) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1405]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10116,plain,
% 7.92/1.49      ( k9_relat_1(sK1,k10_relat_1(sK1,X0)) != k9_relat_1(sK1,k10_relat_1(sK1,X0))
% 7.92/1.49      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1))))
% 7.92/1.49      | k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) != k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_3310]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_11862,plain,
% 7.92/1.49      ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 7.92/1.49      | k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))))
% 7.92/1.49      | k6_subset_1(k9_relat_1(sK1,sK0),k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))) != k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_10116]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_340,plain,( X0 = X0 ),theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1399,plain,
% 7.92/1.49      ( k9_relat_1(sK1,X0) = k9_relat_1(sK1,X0) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_340]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3086,plain,
% 7.92/1.49      ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1399]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1293,plain,
% 7.92/1.49      ( k9_relat_1(sK1,sK0) = k9_relat_1(sK1,sK0) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_340]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9,plain,
% 7.92/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_239,plain,
% 7.92/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | sK1 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_240,plain,
% 7.92/1.49      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_239]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_712,plain,
% 7.92/1.49      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_240]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_14,plain,
% 7.92/1.49      ( r1_tarski(X0,X1)
% 7.92/1.49      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.92/1.49      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.92/1.49      | ~ v1_funct_1(X2)
% 7.92/1.49      | ~ v2_funct_1(X2)
% 7.92/1.49      | ~ v1_relat_1(X2) ),
% 7.92/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_16,negated_conjecture,
% 7.92/1.49      ( v2_funct_1(sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_185,plain,
% 7.92/1.49      ( r1_tarski(X0,X1)
% 7.92/1.49      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.92/1.49      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.92/1.49      | ~ v1_funct_1(X2)
% 7.92/1.49      | ~ v1_relat_1(X2)
% 7.92/1.49      | sK1 != X2 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_186,plain,
% 7.92/1.49      ( r1_tarski(X0,X1)
% 7.92/1.49      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 7.92/1.49      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
% 7.92/1.49      | ~ v1_funct_1(sK1)
% 7.92/1.49      | ~ v1_relat_1(sK1) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_185]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_188,plain,
% 7.92/1.49      ( r1_tarski(X0,X1)
% 7.92/1.49      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 7.92/1.49      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_186,c_19,c_18]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_686,plain,
% 7.92/1.49      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
% 7.92/1.49      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 7.92/1.49      | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_188]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_0,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.92/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_606,plain,
% 7.92/1.49      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 7.92/1.49      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 7.92/1.49      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_12,plain,
% 7.92/1.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.92/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.92/1.49      | ~ v1_relat_1(X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_253,plain,
% 7.92/1.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.92/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.92/1.49      | sK1 != X1 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_254,plain,
% 7.92/1.49      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
% 7.92/1.49      | ~ r1_tarski(X0,k1_relat_1(sK1)) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_253]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_549,plain,
% 7.92/1.49      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 7.92/1.49      | ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_254]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_15,negated_conjecture,
% 7.92/1.49      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_17,negated_conjecture,
% 7.92/1.49      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(contradiction,plain,
% 7.92/1.49      ( $false ),
% 7.92/1.49      inference(minisat,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_27944,c_27940,c_11864,c_11862,c_3086,c_1293,c_712,
% 7.92/1.49                 c_686,c_606,c_549,c_15,c_17]) ).
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  ------                               Statistics
% 7.92/1.49  
% 7.92/1.49  ------ Selected
% 7.92/1.49  
% 7.92/1.49  total_time:                             0.822
% 7.92/1.49  
%------------------------------------------------------------------------------
