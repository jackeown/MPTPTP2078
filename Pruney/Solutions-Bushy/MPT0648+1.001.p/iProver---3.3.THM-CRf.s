%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0648+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:48 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 137 expanded)
%              Number of clauses        :   23 (  38 expanded)
%              Number of leaves         :    4 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 ( 550 expanded)
%              Number of equality atoms :   51 ( 216 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
            & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) != k1_relat_1(X0)
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) != k1_relat_1(X0)
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0] :
        ( ( k2_relat_1(k2_funct_1(X0)) != k1_relat_1(X0)
          | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(k2_funct_1(sK0)) != k1_relat_1(sK0)
        | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ( k2_relat_1(k2_funct_1(sK0)) != k1_relat_1(sK0)
      | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f18,plain,
    ( k2_relat_1(k2_funct_1(sK0)) != k1_relat_1(sK0)
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_3,negated_conjecture,
    ( k2_relat_1(k2_funct_1(sK0)) != k1_relat_1(sK0)
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_102,negated_conjecture,
    ( k2_relat_1(k2_funct_1(sK0)) != k1_relat_1(sK0)
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_81,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_82,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_81])).

cnf(c_100,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_82])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_4,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_72,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_73,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k4_relat_1(sK0) = k2_funct_1(sK0) ),
    inference(unflattening,[status(thm)],[c_72])).

cnf(c_5,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_17,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k4_relat_1(sK0) = k2_funct_1(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_75,plain,
    ( k4_relat_1(sK0) = k2_funct_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73,c_6,c_5,c_4,c_17])).

cnf(c_101,plain,
    ( k4_relat_1(sK0) = k2_funct_1(sK0) ),
    inference(subtyping,[status(esa)],[c_75])).

cnf(c_119,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_100,c_101])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_86,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_87,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_86])).

cnf(c_99,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_87])).

cnf(c_122,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_99,c_101])).

cnf(c_125,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_102,c_119,c_122])).

cnf(c_126,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_125])).


%------------------------------------------------------------------------------
