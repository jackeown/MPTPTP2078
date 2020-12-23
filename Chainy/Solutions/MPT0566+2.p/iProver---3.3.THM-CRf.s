%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0566+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 23.50s
% Output     : CNFRefutation 23.50s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f750,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1378,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f3103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1378])).

fof(f753,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f754,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f753])).

fof(f1381,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f754])).

fof(f1912,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK160,sK159),k10_relat_1(sK160,k2_relat_1(sK160)))
      & v1_relat_1(sK160) ) ),
    introduced(choice_axiom,[])).

fof(f1913,plain,
    ( ~ r1_tarski(k10_relat_1(sK160,sK159),k10_relat_1(sK160,k2_relat_1(sK160)))
    & v1_relat_1(sK160) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK159,sK160])],[f1381,f1912])).

fof(f3106,plain,(
    v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f1913])).

fof(f752,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1380,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f752])).

fof(f3105,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1380])).

fof(f3107,plain,(
    ~ r1_tarski(k10_relat_1(sK160,sK159),k10_relat_1(sK160,k2_relat_1(sK160))) ),
    inference(cnf_transformation,[],[f1913])).

cnf(c_33327,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_58054,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(sK160,sK159),k10_relat_1(sK160,k2_relat_1(sK160)))
    | k10_relat_1(sK160,k2_relat_1(sK160)) != X1
    | k10_relat_1(sK160,sK159) != X0 ),
    inference(instantiation,[status(thm)],[c_33327])).

cnf(c_67891,plain,
    ( ~ r1_tarski(k10_relat_1(sK160,sK159),X0)
    | r1_tarski(k10_relat_1(sK160,sK159),k10_relat_1(sK160,k2_relat_1(sK160)))
    | k10_relat_1(sK160,k2_relat_1(sK160)) != X0
    | k10_relat_1(sK160,sK159) != k10_relat_1(sK160,sK159) ),
    inference(instantiation,[status(thm)],[c_58054])).

cnf(c_91599,plain,
    ( r1_tarski(k10_relat_1(sK160,sK159),k10_relat_1(sK160,k2_relat_1(sK160)))
    | ~ r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160))
    | k10_relat_1(sK160,k2_relat_1(sK160)) != k1_relat_1(sK160)
    | k10_relat_1(sK160,sK159) != k10_relat_1(sK160,sK159) ),
    inference(instantiation,[status(thm)],[c_67891])).

cnf(c_33319,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_67892,plain,
    ( k10_relat_1(sK160,sK159) = k10_relat_1(sK160,sK159) ),
    inference(instantiation,[status(thm)],[c_33319])).

cnf(c_1159,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3103])).

cnf(c_67228,plain,
    ( r1_tarski(k10_relat_1(sK160,sK159),k1_relat_1(sK160))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_1163,negated_conjecture,
    ( v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f3106])).

cnf(c_52341,plain,
    ( v1_relat_1(sK160) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_1161,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3105])).

cnf(c_52343,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_64892,plain,
    ( k10_relat_1(sK160,k2_relat_1(sK160)) = k1_relat_1(sK160) ),
    inference(superposition,[status(thm)],[c_52341,c_52343])).

cnf(c_1162,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK160,sK159),k10_relat_1(sK160,k2_relat_1(sK160))) ),
    inference(cnf_transformation,[],[f3107])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91599,c_67892,c_67228,c_64892,c_1162,c_1163])).

%------------------------------------------------------------------------------
