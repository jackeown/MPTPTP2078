%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0452+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:20 EST 2020

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of clauses        :   44 (  54 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  133 ( 194 expanded)
%              Number of equality atoms :   98 ( 138 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0] :
      ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,
    ( ? [X0] :
        ( k3_relat_1(X0) != k3_relat_1(k4_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f19,plain,(
    k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_75,plain,
    ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_647,plain,
    ( k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0))) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_78,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_232,plain,
    ( X0_36 != X1_36
    | k3_relat_1(k4_relat_1(sK0)) != X1_36
    | k3_relat_1(k4_relat_1(sK0)) = X0_36 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_546,plain,
    ( X0_36 != k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0)))
    | k3_relat_1(k4_relat_1(sK0)) = X0_36
    | k3_relat_1(k4_relat_1(sK0)) != k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_646,plain,
    ( k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0))) != k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0)))
    | k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)))
    | k3_relat_1(k4_relat_1(sK0)) != k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_177,plain,
    ( k3_relat_1(k4_relat_1(sK0)) != X0_36
    | k3_relat_1(sK0) != X0_36
    | k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_589,plain,
    ( k3_relat_1(k4_relat_1(sK0)) != k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)))
    | k3_relat_1(sK0) = k3_relat_1(k4_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_184,plain,
    ( X0_36 != X1_36
    | k3_relat_1(sK0) != X1_36
    | k3_relat_1(sK0) = X0_36 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_210,plain,
    ( X0_36 != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | k3_relat_1(sK0) = X0_36
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_225,plain,
    ( k2_xboole_0(X0_37,X1_37) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | k3_relat_1(sK0) = k2_xboole_0(X0_37,X1_37)
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_536,plain,
    ( k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0))) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | k3_relat_1(sK0) = k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_299,plain,
    ( X0_36 != k3_relat_1(k4_relat_1(sK0))
    | k3_relat_1(k4_relat_1(sK0)) = X0_36
    | k3_relat_1(k4_relat_1(sK0)) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_386,plain,
    ( k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) != k3_relat_1(k4_relat_1(sK0))
    | k3_relat_1(k4_relat_1(sK0)) = k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0)))
    | k3_relat_1(k4_relat_1(sK0)) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_80,plain,
    ( X0_37 != X1_37
    | X2_37 != X3_37
    | k2_xboole_0(X0_37,X2_37) = k2_xboole_0(X1_37,X3_37) ),
    theory(equality)).

cnf(c_226,plain,
    ( X0_37 != k2_relat_1(sK0)
    | X1_37 != k1_relat_1(sK0)
    | k2_xboole_0(X1_37,X0_37) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_286,plain,
    ( X0_37 != k1_relat_1(sK0)
    | k1_relat_1(k4_relat_1(sK0)) != k2_relat_1(sK0)
    | k2_xboole_0(X0_37,k1_relat_1(k4_relat_1(sK0))) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_374,plain,
    ( k2_relat_1(k4_relat_1(sK0)) != k1_relat_1(sK0)
    | k1_relat_1(k4_relat_1(sK0)) != k2_relat_1(sK0)
    | k2_xboole_0(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0))) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_73,plain,
    ( ~ v1_relat_1(X0_35)
    | v1_relat_1(k4_relat_1(X0_35)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_141,plain,
    ( v1_relat_1(X0_35) != iProver_top
    | v1_relat_1(k4_relat_1(X0_35)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_74,plain,
    ( ~ v1_relat_1(X0_35)
    | k2_xboole_0(k1_relat_1(X0_35),k2_relat_1(X0_35)) = k3_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_140,plain,
    ( k2_xboole_0(k1_relat_1(X0_35),k2_relat_1(X0_35)) = k3_relat_1(X0_35)
    | v1_relat_1(X0_35) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_357,plain,
    ( k2_xboole_0(k1_relat_1(k4_relat_1(X0_35)),k2_relat_1(k4_relat_1(X0_35))) = k3_relat_1(k4_relat_1(X0_35))
    | v1_relat_1(X0_35) != iProver_top ),
    inference(superposition,[status(thm)],[c_141,c_140])).

cnf(c_365,plain,
    ( k2_xboole_0(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) = k3_relat_1(k4_relat_1(sK0))
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_76,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_231,plain,
    ( k3_relat_1(k4_relat_1(sK0)) = k3_relat_1(k4_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_191,plain,
    ( X0_36 != k3_relat_1(sK0)
    | k3_relat_1(sK0) = X0_36
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_200,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) != k3_relat_1(sK0)
    | k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | k3_relat_1(sK0) != k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_183,plain,
    ( k3_relat_1(sK0) = k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_5,negated_conjecture,
    ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_70,negated_conjecture,
    ( k3_relat_1(sK0) != k3_relat_1(k4_relat_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_71,plain,
    ( ~ v1_relat_1(X0_35)
    | k1_relat_1(k4_relat_1(X0_35)) = k2_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_93,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_72,plain,
    ( ~ v1_relat_1(X0_35)
    | k2_relat_1(k4_relat_1(X0_35)) = k1_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_90,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_86,plain,
    ( ~ v1_relat_1(sK0)
    | k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_647,c_646,c_589,c_536,c_386,c_374,c_365,c_231,c_200,c_183,c_70,c_93,c_90,c_86,c_7,c_6])).


%------------------------------------------------------------------------------
