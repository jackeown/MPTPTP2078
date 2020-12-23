%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1093+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Timeout 59.52s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   38 (  91 expanded)
%              Number of clauses        :   19 (  23 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 382 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1740,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v1_finset_1(k10_relat_1(X1,X0))
          & r1_tarski(X0,k2_relat_1(X1)) )
       => v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1741,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v1_finset_1(k10_relat_1(X1,X0))
            & r1_tarski(X0,k2_relat_1(X1)) )
         => v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1740])).

fof(f3695,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1741])).

fof(f3696,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f3695])).

fof(f5200,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(k10_relat_1(X1,X0))
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(sK626)
      & v1_finset_1(k10_relat_1(sK627,sK626))
      & r1_tarski(sK626,k2_relat_1(sK627))
      & v1_funct_1(sK627)
      & v1_relat_1(sK627) ) ),
    introduced(choice_axiom,[])).

fof(f5201,plain,
    ( ~ v1_finset_1(sK626)
    & v1_finset_1(k10_relat_1(sK627,sK626))
    & r1_tarski(sK626,k2_relat_1(sK627))
    & v1_funct_1(sK627)
    & v1_relat_1(sK627) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK626,sK627])],[f3696,f5200])).

fof(f8576,plain,(
    r1_tarski(sK626,k2_relat_1(sK627)) ),
    inference(cnf_transformation,[],[f5201])).

fof(f966,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2611,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f966])).

fof(f2612,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2611])).

fof(f6736,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2612])).

fof(f8574,plain,(
    v1_relat_1(sK627) ),
    inference(cnf_transformation,[],[f5201])).

fof(f8575,plain,(
    v1_funct_1(sK627) ),
    inference(cnf_transformation,[],[f5201])).

fof(f1735,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_finset_1(X0)
       => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3688,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1735])).

fof(f3689,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f3688])).

fof(f8565,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3689])).

fof(f8578,plain,(
    ~ v1_finset_1(sK626) ),
    inference(cnf_transformation,[],[f5201])).

fof(f8577,plain,(
    v1_finset_1(k10_relat_1(sK627,sK626)) ),
    inference(cnf_transformation,[],[f5201])).

cnf(c_3348,negated_conjecture,
    ( r1_tarski(sK626,k2_relat_1(sK627)) ),
    inference(cnf_transformation,[],[f8576])).

cnf(c_97129,plain,
    ( r1_tarski(sK626,k2_relat_1(sK627)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3348])).

cnf(c_1520,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f6736])).

cnf(c_98755,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_211385,plain,
    ( k9_relat_1(sK627,k10_relat_1(sK627,sK626)) = sK626
    | v1_funct_1(sK627) != iProver_top
    | v1_relat_1(sK627) != iProver_top ),
    inference(superposition,[status(thm)],[c_97129,c_98755])).

cnf(c_3350,negated_conjecture,
    ( v1_relat_1(sK627) ),
    inference(cnf_transformation,[],[f8574])).

cnf(c_3349,negated_conjecture,
    ( v1_funct_1(sK627) ),
    inference(cnf_transformation,[],[f8575])).

cnf(c_135851,plain,
    ( ~ r1_tarski(sK626,k2_relat_1(sK627))
    | ~ v1_funct_1(sK627)
    | ~ v1_relat_1(sK627)
    | k9_relat_1(sK627,k10_relat_1(sK627,sK626)) = sK626 ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_212392,plain,
    ( k9_relat_1(sK627,k10_relat_1(sK627,sK626)) = sK626 ),
    inference(global_propositional_subsumption,[status(thm)],[c_211385,c_3350,c_3349,c_3348,c_135851])).

cnf(c_3337,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k9_relat_1(X1,X0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f8565])).

cnf(c_97194,plain,
    ( v1_finset_1(X0) != iProver_top
    | v1_finset_1(k9_relat_1(X1,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3337])).

cnf(c_212402,plain,
    ( v1_finset_1(k10_relat_1(sK627,sK626)) != iProver_top
    | v1_finset_1(sK626) = iProver_top
    | v1_funct_1(sK627) != iProver_top
    | v1_relat_1(sK627) != iProver_top ),
    inference(superposition,[status(thm)],[c_212392,c_97194])).

cnf(c_3346,negated_conjecture,
    ( ~ v1_finset_1(sK626) ),
    inference(cnf_transformation,[],[f8578])).

cnf(c_3355,plain,
    ( v1_finset_1(sK626) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3346])).

cnf(c_3347,negated_conjecture,
    ( v1_finset_1(k10_relat_1(sK627,sK626)) ),
    inference(cnf_transformation,[],[f8577])).

cnf(c_3354,plain,
    ( v1_finset_1(k10_relat_1(sK627,sK626)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3347])).

cnf(c_3352,plain,
    ( v1_funct_1(sK627) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3349])).

cnf(c_3351,plain,
    ( v1_relat_1(sK627) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_212402,c_3355,c_3354,c_3352,c_3351])).

%------------------------------------------------------------------------------
