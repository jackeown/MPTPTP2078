%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0672+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:49 EST 2020

% Result     : Theorem 23.66s
% Output     : CNFRefutation 23.66s
% Verified   : 
% Statistics : Number of formulae       :   33 (  63 expanded)
%              Number of clauses        :   16 (  20 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 237 expanded)
%              Number of equality atoms :   45 ( 103 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f977,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f978,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f977])).

fof(f1858,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f978])).

fof(f1859,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1858])).

fof(f2449,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK212,sK214) != k8_relat_1(sK212,k8_relat_1(sK213,sK214))
        | k8_relat_1(sK212,sK214) != k8_relat_1(sK213,k8_relat_1(sK212,sK214)) )
      & r1_tarski(sK212,sK213)
      & v1_funct_1(sK214)
      & v1_relat_1(sK214) ) ),
    introduced(choice_axiom,[])).

fof(f2450,plain,
    ( ( k8_relat_1(sK212,sK214) != k8_relat_1(sK212,k8_relat_1(sK213,sK214))
      | k8_relat_1(sK212,sK214) != k8_relat_1(sK213,k8_relat_1(sK212,sK214)) )
    & r1_tarski(sK212,sK213)
    & v1_funct_1(sK214)
    & v1_relat_1(sK214) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK212,sK213,sK214])],[f1859,f2449])).

fof(f4048,plain,(
    v1_relat_1(sK214) ),
    inference(cnf_transformation,[],[f2450])).

fof(f4050,plain,(
    r1_tarski(sK212,sK213) ),
    inference(cnf_transformation,[],[f2450])).

fof(f732,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1516,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f1517,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1516])).

fof(f3614,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1517])).

fof(f733,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1518,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f1519,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1518])).

fof(f3615,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1519])).

fof(f4051,plain,
    ( k8_relat_1(sK212,sK214) != k8_relat_1(sK212,k8_relat_1(sK213,sK214))
    | k8_relat_1(sK212,sK214) != k8_relat_1(sK213,k8_relat_1(sK212,sK214)) ),
    inference(cnf_transformation,[],[f2450])).

cnf(c_1584,negated_conjecture,
    ( v1_relat_1(sK214) ),
    inference(cnf_transformation,[],[f4048])).

cnf(c_43427,plain,
    ( v1_relat_1(sK214) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(c_1582,negated_conjecture,
    ( r1_tarski(sK212,sK213) ),
    inference(cnf_transformation,[],[f4050])).

cnf(c_43429,plain,
    ( r1_tarski(sK212,sK213) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1582])).

cnf(c_1147,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f3614])).

cnf(c_43771,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_72221,plain,
    ( k8_relat_1(sK213,k8_relat_1(sK212,X0)) = k8_relat_1(sK212,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_43429,c_43771])).

cnf(c_73087,plain,
    ( k8_relat_1(sK213,k8_relat_1(sK212,sK214)) = k8_relat_1(sK212,sK214) ),
    inference(superposition,[status(thm)],[c_43427,c_72221])).

cnf(c_1148,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f3615])).

cnf(c_43770,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_68231,plain,
    ( k8_relat_1(sK212,k8_relat_1(sK213,X0)) = k8_relat_1(sK212,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_43429,c_43770])).

cnf(c_69459,plain,
    ( k8_relat_1(sK212,k8_relat_1(sK213,sK214)) = k8_relat_1(sK212,sK214) ),
    inference(superposition,[status(thm)],[c_43427,c_68231])).

cnf(c_1581,negated_conjecture,
    ( k8_relat_1(sK212,sK214) != k8_relat_1(sK213,k8_relat_1(sK212,sK214))
    | k8_relat_1(sK212,sK214) != k8_relat_1(sK212,k8_relat_1(sK213,sK214)) ),
    inference(cnf_transformation,[],[f4051])).

cnf(c_69650,plain,
    ( k8_relat_1(sK213,k8_relat_1(sK212,sK214)) != k8_relat_1(sK212,sK214)
    | k8_relat_1(sK212,sK214) != k8_relat_1(sK212,sK214) ),
    inference(demodulation,[status(thm)],[c_69459,c_1581])).

cnf(c_69651,plain,
    ( k8_relat_1(sK213,k8_relat_1(sK212,sK214)) != k8_relat_1(sK212,sK214) ),
    inference(theory_normalisation,[status(thm)],[c_69650])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73087,c_69651])).

%------------------------------------------------------------------------------
