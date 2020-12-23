%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:59 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 219 expanded)
%              Number of clauses        :   79 ( 104 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  300 ( 544 expanded)
%              Number of equality atoms :  139 ( 227 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

cnf(c_253,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_13330,plain,
    ( X0 != X1
    | X0 = k2_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_13331,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13330])).

cnf(c_255,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3956,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X2)
    | X2 != X1
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_7329,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,X0)),X1)
    | r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X2)
    | X2 != X1
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k2_relat_1(k5_relat_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_3956])).

cnf(c_8915,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X0)
    | ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | X0 != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_7329])).

cnf(c_8917,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8915])).

cnf(c_11,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3951,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_505,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_501,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_502,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_768,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_502])).

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_782,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_768,c_14])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_30,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_32,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_48,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1600,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_32,c_48])).

cnf(c_1601,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1600])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_509,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1607,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1601,c_509])).

cnf(c_1612,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_501,c_1607])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_504,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1642,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_504])).

cnf(c_513,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_507,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_512,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_865,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_507,c_512])).

cnf(c_1099,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_513,c_865])).

cnf(c_1654,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1642,c_1099])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_511,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1823,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_511])).

cnf(c_1941,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1823,c_509])).

cnf(c_1943,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_1941])).

cnf(c_17,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3047,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1943,c_17,c_32,c_48])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3061,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3047,c_15])).

cnf(c_3062,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3061])).

cnf(c_2784,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_254,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2725,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_2727,plain,
    ( v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2725])).

cnf(c_2427,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X0)
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2429,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_252,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1853,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1589,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1120,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
    | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_629,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_755,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,X0),X1)
    | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,X0)
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_901,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))
    | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,X0)
    | k1_xboole_0 != k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_904,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
    | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_744,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_716,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_661,plain,
    ( r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_655,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_634,plain,
    ( ~ r1_tarski(X0,k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),X0)
    | k5_relat_1(sK0,k1_xboole_0) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_654,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_636,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
    | k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_43,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_38,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_31,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13331,c_8917,c_3951,c_3062,c_2784,c_2727,c_2429,c_1853,c_1589,c_1120,c_904,c_744,c_716,c_661,c_655,c_654,c_636,c_0,c_43,c_38,c_31,c_13,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.00  
% 3.60/1.00  ------  iProver source info
% 3.60/1.00  
% 3.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.00  git: non_committed_changes: false
% 3.60/1.00  git: last_make_outside_of_git: false
% 3.60/1.00  
% 3.60/1.00  ------ 
% 3.60/1.00  
% 3.60/1.00  ------ Input Options
% 3.60/1.00  
% 3.60/1.00  --out_options                           all
% 3.60/1.00  --tptp_safe_out                         true
% 3.60/1.00  --problem_path                          ""
% 3.60/1.00  --include_path                          ""
% 3.60/1.00  --clausifier                            res/vclausify_rel
% 3.60/1.00  --clausifier_options                    --mode clausify
% 3.60/1.00  --stdin                                 false
% 3.60/1.00  --stats_out                             all
% 3.60/1.00  
% 3.60/1.00  ------ General Options
% 3.60/1.00  
% 3.60/1.00  --fof                                   false
% 3.60/1.00  --time_out_real                         305.
% 3.60/1.00  --time_out_virtual                      -1.
% 3.60/1.00  --symbol_type_check                     false
% 3.60/1.00  --clausify_out                          false
% 3.60/1.00  --sig_cnt_out                           false
% 3.60/1.00  --trig_cnt_out                          false
% 3.60/1.00  --trig_cnt_out_tolerance                1.
% 3.60/1.00  --trig_cnt_out_sk_spl                   false
% 3.60/1.00  --abstr_cl_out                          false
% 3.60/1.00  
% 3.60/1.00  ------ Global Options
% 3.60/1.00  
% 3.60/1.00  --schedule                              default
% 3.60/1.00  --add_important_lit                     false
% 3.60/1.00  --prop_solver_per_cl                    1000
% 3.60/1.00  --min_unsat_core                        false
% 3.60/1.00  --soft_assumptions                      false
% 3.60/1.00  --soft_lemma_size                       3
% 3.60/1.00  --prop_impl_unit_size                   0
% 3.60/1.00  --prop_impl_unit                        []
% 3.60/1.00  --share_sel_clauses                     true
% 3.60/1.00  --reset_solvers                         false
% 3.60/1.00  --bc_imp_inh                            [conj_cone]
% 3.60/1.00  --conj_cone_tolerance                   3.
% 3.60/1.00  --extra_neg_conj                        none
% 3.60/1.00  --large_theory_mode                     true
% 3.60/1.00  --prolific_symb_bound                   200
% 3.60/1.00  --lt_threshold                          2000
% 3.60/1.00  --clause_weak_htbl                      true
% 3.60/1.00  --gc_record_bc_elim                     false
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing Options
% 3.60/1.00  
% 3.60/1.00  --preprocessing_flag                    true
% 3.60/1.00  --time_out_prep_mult                    0.1
% 3.60/1.00  --splitting_mode                        input
% 3.60/1.00  --splitting_grd                         true
% 3.60/1.00  --splitting_cvd                         false
% 3.60/1.00  --splitting_cvd_svl                     false
% 3.60/1.00  --splitting_nvd                         32
% 3.60/1.00  --sub_typing                            true
% 3.60/1.00  --prep_gs_sim                           true
% 3.60/1.00  --prep_unflatten                        true
% 3.60/1.00  --prep_res_sim                          true
% 3.60/1.00  --prep_upred                            true
% 3.60/1.00  --prep_sem_filter                       exhaustive
% 3.60/1.00  --prep_sem_filter_out                   false
% 3.60/1.00  --pred_elim                             true
% 3.60/1.00  --res_sim_input                         true
% 3.60/1.00  --eq_ax_congr_red                       true
% 3.60/1.00  --pure_diseq_elim                       true
% 3.60/1.00  --brand_transform                       false
% 3.60/1.00  --non_eq_to_eq                          false
% 3.60/1.00  --prep_def_merge                        true
% 3.60/1.00  --prep_def_merge_prop_impl              false
% 3.60/1.00  --prep_def_merge_mbd                    true
% 3.60/1.00  --prep_def_merge_tr_red                 false
% 3.60/1.00  --prep_def_merge_tr_cl                  false
% 3.60/1.00  --smt_preprocessing                     true
% 3.60/1.00  --smt_ac_axioms                         fast
% 3.60/1.00  --preprocessed_out                      false
% 3.60/1.00  --preprocessed_stats                    false
% 3.60/1.00  
% 3.60/1.00  ------ Abstraction refinement Options
% 3.60/1.00  
% 3.60/1.00  --abstr_ref                             []
% 3.60/1.00  --abstr_ref_prep                        false
% 3.60/1.00  --abstr_ref_until_sat                   false
% 3.60/1.00  --abstr_ref_sig_restrict                funpre
% 3.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.00  --abstr_ref_under                       []
% 3.60/1.00  
% 3.60/1.00  ------ SAT Options
% 3.60/1.00  
% 3.60/1.00  --sat_mode                              false
% 3.60/1.00  --sat_fm_restart_options                ""
% 3.60/1.00  --sat_gr_def                            false
% 3.60/1.00  --sat_epr_types                         true
% 3.60/1.00  --sat_non_cyclic_types                  false
% 3.60/1.00  --sat_finite_models                     false
% 3.60/1.00  --sat_fm_lemmas                         false
% 3.60/1.00  --sat_fm_prep                           false
% 3.60/1.00  --sat_fm_uc_incr                        true
% 3.60/1.00  --sat_out_model                         small
% 3.60/1.00  --sat_out_clauses                       false
% 3.60/1.00  
% 3.60/1.00  ------ QBF Options
% 3.60/1.00  
% 3.60/1.00  --qbf_mode                              false
% 3.60/1.00  --qbf_elim_univ                         false
% 3.60/1.00  --qbf_dom_inst                          none
% 3.60/1.00  --qbf_dom_pre_inst                      false
% 3.60/1.00  --qbf_sk_in                             false
% 3.60/1.00  --qbf_pred_elim                         true
% 3.60/1.00  --qbf_split                             512
% 3.60/1.00  
% 3.60/1.00  ------ BMC1 Options
% 3.60/1.00  
% 3.60/1.00  --bmc1_incremental                      false
% 3.60/1.00  --bmc1_axioms                           reachable_all
% 3.60/1.00  --bmc1_min_bound                        0
% 3.60/1.00  --bmc1_max_bound                        -1
% 3.60/1.00  --bmc1_max_bound_default                -1
% 3.60/1.00  --bmc1_symbol_reachability              true
% 3.60/1.00  --bmc1_property_lemmas                  false
% 3.60/1.00  --bmc1_k_induction                      false
% 3.60/1.00  --bmc1_non_equiv_states                 false
% 3.60/1.00  --bmc1_deadlock                         false
% 3.60/1.00  --bmc1_ucm                              false
% 3.60/1.00  --bmc1_add_unsat_core                   none
% 3.60/1.00  --bmc1_unsat_core_children              false
% 3.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.00  --bmc1_out_stat                         full
% 3.60/1.00  --bmc1_ground_init                      false
% 3.60/1.00  --bmc1_pre_inst_next_state              false
% 3.60/1.00  --bmc1_pre_inst_state                   false
% 3.60/1.00  --bmc1_pre_inst_reach_state             false
% 3.60/1.00  --bmc1_out_unsat_core                   false
% 3.60/1.00  --bmc1_aig_witness_out                  false
% 3.60/1.00  --bmc1_verbose                          false
% 3.60/1.00  --bmc1_dump_clauses_tptp                false
% 3.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.00  --bmc1_dump_file                        -
% 3.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.00  --bmc1_ucm_extend_mode                  1
% 3.60/1.00  --bmc1_ucm_init_mode                    2
% 3.60/1.00  --bmc1_ucm_cone_mode                    none
% 3.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.00  --bmc1_ucm_relax_model                  4
% 3.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.00  --bmc1_ucm_layered_model                none
% 3.60/1.00  --bmc1_ucm_max_lemma_size               10
% 3.60/1.00  
% 3.60/1.00  ------ AIG Options
% 3.60/1.00  
% 3.60/1.00  --aig_mode                              false
% 3.60/1.00  
% 3.60/1.00  ------ Instantiation Options
% 3.60/1.00  
% 3.60/1.00  --instantiation_flag                    true
% 3.60/1.00  --inst_sos_flag                         false
% 3.60/1.00  --inst_sos_phase                        true
% 3.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.00  --inst_lit_sel_side                     num_symb
% 3.60/1.00  --inst_solver_per_active                1400
% 3.60/1.00  --inst_solver_calls_frac                1.
% 3.60/1.00  --inst_passive_queue_type               priority_queues
% 3.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.00  --inst_passive_queues_freq              [25;2]
% 3.60/1.00  --inst_dismatching                      true
% 3.60/1.00  --inst_eager_unprocessed_to_passive     true
% 3.60/1.00  --inst_prop_sim_given                   true
% 3.60/1.00  --inst_prop_sim_new                     false
% 3.60/1.00  --inst_subs_new                         false
% 3.60/1.00  --inst_eq_res_simp                      false
% 3.60/1.00  --inst_subs_given                       false
% 3.60/1.00  --inst_orphan_elimination               true
% 3.60/1.00  --inst_learning_loop_flag               true
% 3.60/1.00  --inst_learning_start                   3000
% 3.60/1.00  --inst_learning_factor                  2
% 3.60/1.00  --inst_start_prop_sim_after_learn       3
% 3.60/1.00  --inst_sel_renew                        solver
% 3.60/1.00  --inst_lit_activity_flag                true
% 3.60/1.00  --inst_restr_to_given                   false
% 3.60/1.00  --inst_activity_threshold               500
% 3.60/1.00  --inst_out_proof                        true
% 3.60/1.00  
% 3.60/1.00  ------ Resolution Options
% 3.60/1.00  
% 3.60/1.00  --resolution_flag                       true
% 3.60/1.00  --res_lit_sel                           adaptive
% 3.60/1.00  --res_lit_sel_side                      none
% 3.60/1.00  --res_ordering                          kbo
% 3.60/1.00  --res_to_prop_solver                    active
% 3.60/1.00  --res_prop_simpl_new                    false
% 3.60/1.00  --res_prop_simpl_given                  true
% 3.60/1.00  --res_passive_queue_type                priority_queues
% 3.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.00  --res_passive_queues_freq               [15;5]
% 3.60/1.00  --res_forward_subs                      full
% 3.60/1.00  --res_backward_subs                     full
% 3.60/1.00  --res_forward_subs_resolution           true
% 3.60/1.00  --res_backward_subs_resolution          true
% 3.60/1.00  --res_orphan_elimination                true
% 3.60/1.00  --res_time_limit                        2.
% 3.60/1.00  --res_out_proof                         true
% 3.60/1.00  
% 3.60/1.00  ------ Superposition Options
% 3.60/1.00  
% 3.60/1.00  --superposition_flag                    true
% 3.60/1.00  --sup_passive_queue_type                priority_queues
% 3.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.00  --demod_completeness_check              fast
% 3.60/1.00  --demod_use_ground                      true
% 3.60/1.00  --sup_to_prop_solver                    passive
% 3.60/1.00  --sup_prop_simpl_new                    true
% 3.60/1.00  --sup_prop_simpl_given                  true
% 3.60/1.00  --sup_fun_splitting                     false
% 3.60/1.00  --sup_smt_interval                      50000
% 3.60/1.00  
% 3.60/1.00  ------ Superposition Simplification Setup
% 3.60/1.00  
% 3.60/1.00  --sup_indices_passive                   []
% 3.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.00  --sup_full_bw                           [BwDemod]
% 3.60/1.00  --sup_immed_triv                        [TrivRules]
% 3.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.00  --sup_immed_bw_main                     []
% 3.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.00  
% 3.60/1.00  ------ Combination Options
% 3.60/1.00  
% 3.60/1.00  --comb_res_mult                         3
% 3.60/1.00  --comb_sup_mult                         2
% 3.60/1.00  --comb_inst_mult                        10
% 3.60/1.00  
% 3.60/1.00  ------ Debug Options
% 3.60/1.00  
% 3.60/1.00  --dbg_backtrace                         false
% 3.60/1.00  --dbg_dump_prop_clauses                 false
% 3.60/1.00  --dbg_dump_prop_clauses_file            -
% 3.60/1.00  --dbg_out_stat                          false
% 3.60/1.00  ------ Parsing...
% 3.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.00  ------ Proving...
% 3.60/1.00  ------ Problem Properties 
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  clauses                                 16
% 3.60/1.00  conjectures                             2
% 3.60/1.00  EPR                                     7
% 3.60/1.00  Horn                                    16
% 3.60/1.00  unary                                   6
% 3.60/1.00  binary                                  6
% 3.60/1.00  lits                                    31
% 3.60/1.00  lits eq                                 7
% 3.60/1.00  fd_pure                                 0
% 3.60/1.00  fd_pseudo                               0
% 3.60/1.00  fd_cond                                 1
% 3.60/1.00  fd_pseudo_cond                          1
% 3.60/1.00  AC symbols                              0
% 3.60/1.00  
% 3.60/1.00  ------ Schedule dynamic 5 is on 
% 3.60/1.00  
% 3.60/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  ------ 
% 3.60/1.00  Current options:
% 3.60/1.00  ------ 
% 3.60/1.00  
% 3.60/1.00  ------ Input Options
% 3.60/1.00  
% 3.60/1.00  --out_options                           all
% 3.60/1.00  --tptp_safe_out                         true
% 3.60/1.00  --problem_path                          ""
% 3.60/1.00  --include_path                          ""
% 3.60/1.00  --clausifier                            res/vclausify_rel
% 3.60/1.00  --clausifier_options                    --mode clausify
% 3.60/1.00  --stdin                                 false
% 3.60/1.00  --stats_out                             all
% 3.60/1.00  
% 3.60/1.00  ------ General Options
% 3.60/1.00  
% 3.60/1.00  --fof                                   false
% 3.60/1.00  --time_out_real                         305.
% 3.60/1.00  --time_out_virtual                      -1.
% 3.60/1.00  --symbol_type_check                     false
% 3.60/1.00  --clausify_out                          false
% 3.60/1.00  --sig_cnt_out                           false
% 3.60/1.00  --trig_cnt_out                          false
% 3.60/1.00  --trig_cnt_out_tolerance                1.
% 3.60/1.00  --trig_cnt_out_sk_spl                   false
% 3.60/1.00  --abstr_cl_out                          false
% 3.60/1.00  
% 3.60/1.00  ------ Global Options
% 3.60/1.00  
% 3.60/1.00  --schedule                              default
% 3.60/1.00  --add_important_lit                     false
% 3.60/1.00  --prop_solver_per_cl                    1000
% 3.60/1.00  --min_unsat_core                        false
% 3.60/1.00  --soft_assumptions                      false
% 3.60/1.00  --soft_lemma_size                       3
% 3.60/1.00  --prop_impl_unit_size                   0
% 3.60/1.00  --prop_impl_unit                        []
% 3.60/1.00  --share_sel_clauses                     true
% 3.60/1.00  --reset_solvers                         false
% 3.60/1.00  --bc_imp_inh                            [conj_cone]
% 3.60/1.00  --conj_cone_tolerance                   3.
% 3.60/1.00  --extra_neg_conj                        none
% 3.60/1.00  --large_theory_mode                     true
% 3.60/1.00  --prolific_symb_bound                   200
% 3.60/1.00  --lt_threshold                          2000
% 3.60/1.00  --clause_weak_htbl                      true
% 3.60/1.00  --gc_record_bc_elim                     false
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing Options
% 3.60/1.00  
% 3.60/1.00  --preprocessing_flag                    true
% 3.60/1.00  --time_out_prep_mult                    0.1
% 3.60/1.00  --splitting_mode                        input
% 3.60/1.00  --splitting_grd                         true
% 3.60/1.00  --splitting_cvd                         false
% 3.60/1.00  --splitting_cvd_svl                     false
% 3.60/1.00  --splitting_nvd                         32
% 3.60/1.00  --sub_typing                            true
% 3.60/1.00  --prep_gs_sim                           true
% 3.60/1.00  --prep_unflatten                        true
% 3.60/1.00  --prep_res_sim                          true
% 3.60/1.00  --prep_upred                            true
% 3.60/1.00  --prep_sem_filter                       exhaustive
% 3.60/1.00  --prep_sem_filter_out                   false
% 3.60/1.00  --pred_elim                             true
% 3.60/1.00  --res_sim_input                         true
% 3.60/1.00  --eq_ax_congr_red                       true
% 3.60/1.00  --pure_diseq_elim                       true
% 3.60/1.00  --brand_transform                       false
% 3.60/1.00  --non_eq_to_eq                          false
% 3.60/1.00  --prep_def_merge                        true
% 3.60/1.00  --prep_def_merge_prop_impl              false
% 3.60/1.00  --prep_def_merge_mbd                    true
% 3.60/1.00  --prep_def_merge_tr_red                 false
% 3.60/1.00  --prep_def_merge_tr_cl                  false
% 3.60/1.00  --smt_preprocessing                     true
% 3.60/1.00  --smt_ac_axioms                         fast
% 3.60/1.00  --preprocessed_out                      false
% 3.60/1.00  --preprocessed_stats                    false
% 3.60/1.00  
% 3.60/1.00  ------ Abstraction refinement Options
% 3.60/1.00  
% 3.60/1.00  --abstr_ref                             []
% 3.60/1.00  --abstr_ref_prep                        false
% 3.60/1.00  --abstr_ref_until_sat                   false
% 3.60/1.00  --abstr_ref_sig_restrict                funpre
% 3.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.00  --abstr_ref_under                       []
% 3.60/1.00  
% 3.60/1.00  ------ SAT Options
% 3.60/1.00  
% 3.60/1.00  --sat_mode                              false
% 3.60/1.00  --sat_fm_restart_options                ""
% 3.60/1.00  --sat_gr_def                            false
% 3.60/1.00  --sat_epr_types                         true
% 3.60/1.00  --sat_non_cyclic_types                  false
% 3.60/1.00  --sat_finite_models                     false
% 3.60/1.00  --sat_fm_lemmas                         false
% 3.60/1.00  --sat_fm_prep                           false
% 3.60/1.00  --sat_fm_uc_incr                        true
% 3.60/1.00  --sat_out_model                         small
% 3.60/1.00  --sat_out_clauses                       false
% 3.60/1.00  
% 3.60/1.00  ------ QBF Options
% 3.60/1.00  
% 3.60/1.00  --qbf_mode                              false
% 3.60/1.00  --qbf_elim_univ                         false
% 3.60/1.00  --qbf_dom_inst                          none
% 3.60/1.00  --qbf_dom_pre_inst                      false
% 3.60/1.00  --qbf_sk_in                             false
% 3.60/1.00  --qbf_pred_elim                         true
% 3.60/1.00  --qbf_split                             512
% 3.60/1.00  
% 3.60/1.00  ------ BMC1 Options
% 3.60/1.00  
% 3.60/1.00  --bmc1_incremental                      false
% 3.60/1.00  --bmc1_axioms                           reachable_all
% 3.60/1.00  --bmc1_min_bound                        0
% 3.60/1.00  --bmc1_max_bound                        -1
% 3.60/1.00  --bmc1_max_bound_default                -1
% 3.60/1.00  --bmc1_symbol_reachability              true
% 3.60/1.00  --bmc1_property_lemmas                  false
% 3.60/1.00  --bmc1_k_induction                      false
% 3.60/1.00  --bmc1_non_equiv_states                 false
% 3.60/1.00  --bmc1_deadlock                         false
% 3.60/1.00  --bmc1_ucm                              false
% 3.60/1.00  --bmc1_add_unsat_core                   none
% 3.60/1.00  --bmc1_unsat_core_children              false
% 3.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.00  --bmc1_out_stat                         full
% 3.60/1.00  --bmc1_ground_init                      false
% 3.60/1.00  --bmc1_pre_inst_next_state              false
% 3.60/1.00  --bmc1_pre_inst_state                   false
% 3.60/1.00  --bmc1_pre_inst_reach_state             false
% 3.60/1.00  --bmc1_out_unsat_core                   false
% 3.60/1.00  --bmc1_aig_witness_out                  false
% 3.60/1.00  --bmc1_verbose                          false
% 3.60/1.00  --bmc1_dump_clauses_tptp                false
% 3.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.00  --bmc1_dump_file                        -
% 3.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.00  --bmc1_ucm_extend_mode                  1
% 3.60/1.00  --bmc1_ucm_init_mode                    2
% 3.60/1.00  --bmc1_ucm_cone_mode                    none
% 3.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.00  --bmc1_ucm_relax_model                  4
% 3.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.00  --bmc1_ucm_layered_model                none
% 3.60/1.00  --bmc1_ucm_max_lemma_size               10
% 3.60/1.00  
% 3.60/1.00  ------ AIG Options
% 3.60/1.00  
% 3.60/1.00  --aig_mode                              false
% 3.60/1.00  
% 3.60/1.00  ------ Instantiation Options
% 3.60/1.00  
% 3.60/1.00  --instantiation_flag                    true
% 3.60/1.00  --inst_sos_flag                         false
% 3.60/1.00  --inst_sos_phase                        true
% 3.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.00  --inst_lit_sel_side                     none
% 3.60/1.00  --inst_solver_per_active                1400
% 3.60/1.00  --inst_solver_calls_frac                1.
% 3.60/1.00  --inst_passive_queue_type               priority_queues
% 3.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.00  --inst_passive_queues_freq              [25;2]
% 3.60/1.00  --inst_dismatching                      true
% 3.60/1.00  --inst_eager_unprocessed_to_passive     true
% 3.60/1.00  --inst_prop_sim_given                   true
% 3.60/1.00  --inst_prop_sim_new                     false
% 3.60/1.00  --inst_subs_new                         false
% 3.60/1.00  --inst_eq_res_simp                      false
% 3.60/1.00  --inst_subs_given                       false
% 3.60/1.00  --inst_orphan_elimination               true
% 3.60/1.00  --inst_learning_loop_flag               true
% 3.60/1.00  --inst_learning_start                   3000
% 3.60/1.00  --inst_learning_factor                  2
% 3.60/1.00  --inst_start_prop_sim_after_learn       3
% 3.60/1.00  --inst_sel_renew                        solver
% 3.60/1.00  --inst_lit_activity_flag                true
% 3.60/1.00  --inst_restr_to_given                   false
% 3.60/1.00  --inst_activity_threshold               500
% 3.60/1.00  --inst_out_proof                        true
% 3.60/1.00  
% 3.60/1.00  ------ Resolution Options
% 3.60/1.00  
% 3.60/1.00  --resolution_flag                       false
% 3.60/1.00  --res_lit_sel                           adaptive
% 3.60/1.00  --res_lit_sel_side                      none
% 3.60/1.00  --res_ordering                          kbo
% 3.60/1.00  --res_to_prop_solver                    active
% 3.60/1.00  --res_prop_simpl_new                    false
% 3.60/1.00  --res_prop_simpl_given                  true
% 3.60/1.00  --res_passive_queue_type                priority_queues
% 3.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.00  --res_passive_queues_freq               [15;5]
% 3.60/1.00  --res_forward_subs                      full
% 3.60/1.00  --res_backward_subs                     full
% 3.60/1.00  --res_forward_subs_resolution           true
% 3.60/1.00  --res_backward_subs_resolution          true
% 3.60/1.00  --res_orphan_elimination                true
% 3.60/1.00  --res_time_limit                        2.
% 3.60/1.00  --res_out_proof                         true
% 3.60/1.00  
% 3.60/1.00  ------ Superposition Options
% 3.60/1.00  
% 3.60/1.00  --superposition_flag                    true
% 3.60/1.00  --sup_passive_queue_type                priority_queues
% 3.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.00  --demod_completeness_check              fast
% 3.60/1.00  --demod_use_ground                      true
% 3.60/1.00  --sup_to_prop_solver                    passive
% 3.60/1.00  --sup_prop_simpl_new                    true
% 3.60/1.00  --sup_prop_simpl_given                  true
% 3.60/1.00  --sup_fun_splitting                     false
% 3.60/1.00  --sup_smt_interval                      50000
% 3.60/1.00  
% 3.60/1.00  ------ Superposition Simplification Setup
% 3.60/1.00  
% 3.60/1.00  --sup_indices_passive                   []
% 3.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.00  --sup_full_bw                           [BwDemod]
% 3.60/1.00  --sup_immed_triv                        [TrivRules]
% 3.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.00  --sup_immed_bw_main                     []
% 3.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.00  
% 3.60/1.00  ------ Combination Options
% 3.60/1.00  
% 3.60/1.00  --comb_res_mult                         3
% 3.60/1.00  --comb_sup_mult                         2
% 3.60/1.00  --comb_inst_mult                        10
% 3.60/1.00  
% 3.60/1.00  ------ Debug Options
% 3.60/1.00  
% 3.60/1.00  --dbg_backtrace                         false
% 3.60/1.00  --dbg_dump_prop_clauses                 false
% 3.60/1.00  --dbg_dump_prop_clauses_file            -
% 3.60/1.00  --dbg_out_stat                          false
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  ------ Proving...
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  % SZS status Theorem for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  fof(f10,axiom,(
% 3.60/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f22,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f10])).
% 3.60/1.00  
% 3.60/1.00  fof(f41,plain,(
% 3.60/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f22])).
% 3.60/1.00  
% 3.60/1.00  fof(f8,axiom,(
% 3.60/1.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f19,plain,(
% 3.60/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.60/1.00    inference(ennf_transformation,[],[f8])).
% 3.60/1.00  
% 3.60/1.00  fof(f20,plain,(
% 3.60/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.60/1.00    inference(flattening,[],[f19])).
% 3.60/1.00  
% 3.60/1.00  fof(f39,plain,(
% 3.60/1.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f20])).
% 3.60/1.00  
% 3.60/1.00  fof(f13,conjecture,(
% 3.60/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f14,negated_conjecture,(
% 3.60/1.00    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.60/1.00    inference(negated_conjecture,[],[f13])).
% 3.60/1.00  
% 3.60/1.00  fof(f25,plain,(
% 3.60/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f14])).
% 3.60/1.00  
% 3.60/1.00  fof(f28,plain,(
% 3.60/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f29,plain,(
% 3.60/1.00    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f28])).
% 3.60/1.00  
% 3.60/1.00  fof(f45,plain,(
% 3.60/1.00    v1_relat_1(sK0)),
% 3.60/1.00    inference(cnf_transformation,[],[f29])).
% 3.60/1.00  
% 3.60/1.00  fof(f12,axiom,(
% 3.60/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f44,plain,(
% 3.60/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.60/1.00    inference(cnf_transformation,[],[f12])).
% 3.60/1.00  
% 3.60/1.00  fof(f11,axiom,(
% 3.60/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f23,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f11])).
% 3.60/1.00  
% 3.60/1.00  fof(f24,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.00    inference(flattening,[],[f23])).
% 3.60/1.00  
% 3.60/1.00  fof(f42,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f24])).
% 3.60/1.00  
% 3.60/1.00  fof(f43,plain,(
% 3.60/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.60/1.00    inference(cnf_transformation,[],[f12])).
% 3.60/1.00  
% 3.60/1.00  fof(f7,axiom,(
% 3.60/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f18,plain,(
% 3.60/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f7])).
% 3.60/1.00  
% 3.60/1.00  fof(f38,plain,(
% 3.60/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f18])).
% 3.60/1.00  
% 3.60/1.00  fof(f1,axiom,(
% 3.60/1.00    v1_xboole_0(k1_xboole_0)),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f30,plain,(
% 3.60/1.00    v1_xboole_0(k1_xboole_0)),
% 3.60/1.00    inference(cnf_transformation,[],[f1])).
% 3.60/1.00  
% 3.60/1.00  fof(f4,axiom,(
% 3.60/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f35,plain,(
% 3.60/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f4])).
% 3.60/1.00  
% 3.60/1.00  fof(f9,axiom,(
% 3.60/1.00    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f21,plain,(
% 3.60/1.00    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f9])).
% 3.60/1.00  
% 3.60/1.00  fof(f40,plain,(
% 3.60/1.00    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f21])).
% 3.60/1.00  
% 3.60/1.00  fof(f6,axiom,(
% 3.60/1.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f17,plain,(
% 3.60/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f6])).
% 3.60/1.00  
% 3.60/1.00  fof(f37,plain,(
% 3.60/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f17])).
% 3.60/1.01  
% 3.60/1.01  fof(f2,axiom,(
% 3.60/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f15,plain,(
% 3.60/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.60/1.01    inference(ennf_transformation,[],[f2])).
% 3.60/1.01  
% 3.60/1.01  fof(f31,plain,(
% 3.60/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f15])).
% 3.60/1.01  
% 3.60/1.01  fof(f3,axiom,(
% 3.60/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f26,plain,(
% 3.60/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/1.01    inference(nnf_transformation,[],[f3])).
% 3.60/1.01  
% 3.60/1.01  fof(f27,plain,(
% 3.60/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/1.01    inference(flattening,[],[f26])).
% 3.60/1.01  
% 3.60/1.01  fof(f34,plain,(
% 3.60/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f27])).
% 3.60/1.01  
% 3.60/1.01  fof(f46,plain,(
% 3.60/1.01    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.60/1.01    inference(cnf_transformation,[],[f29])).
% 3.60/1.01  
% 3.60/1.01  fof(f5,axiom,(
% 3.60/1.01    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f16,plain,(
% 3.60/1.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.60/1.01    inference(ennf_transformation,[],[f5])).
% 3.60/1.01  
% 3.60/1.01  fof(f36,plain,(
% 3.60/1.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f16])).
% 3.60/1.01  
% 3.60/1.01  fof(f32,plain,(
% 3.60/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.60/1.01    inference(cnf_transformation,[],[f27])).
% 3.60/1.01  
% 3.60/1.01  fof(f48,plain,(
% 3.60/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.60/1.01    inference(equality_resolution,[],[f32])).
% 3.60/1.01  
% 3.60/1.01  cnf(c_253,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_13330,plain,
% 3.60/1.01      ( X0 != X1
% 3.60/1.01      | X0 = k2_relat_1(k1_xboole_0)
% 3.60/1.01      | k2_relat_1(k1_xboole_0) != X1 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_253]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_13331,plain,
% 3.60/1.01      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.60/1.01      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 3.60/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_13330]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_255,plain,
% 3.60/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.60/1.01      theory(equality) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3956,plain,
% 3.60/1.01      ( ~ r1_tarski(X0,X1)
% 3.60/1.01      | r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X2)
% 3.60/1.01      | X2 != X1
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_255]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_7329,plain,
% 3.60/1.01      ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,X0)),X1)
% 3.60/1.01      | r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X2)
% 3.60/1.01      | X2 != X1
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k2_relat_1(k5_relat_1(sK0,X0)) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_3956]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8915,plain,
% 3.60/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X0)
% 3.60/1.01      | ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
% 3.60/1.01      | X0 != k2_relat_1(k1_xboole_0)
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_7329]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8917,plain,
% 3.60/1.01      ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
% 3.60/1.01      | r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 3.60/1.01      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_8915]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_11,plain,
% 3.60/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.60/1.01      | ~ v1_relat_1(X1)
% 3.60/1.01      | ~ v1_relat_1(X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3951,plain,
% 3.60/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
% 3.60/1.01      | ~ v1_relat_1(sK0)
% 3.60/1.01      | ~ v1_relat_1(k1_xboole_0) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_9,plain,
% 3.60/1.01      ( ~ v1_relat_1(X0)
% 3.60/1.01      | ~ v1_relat_1(X1)
% 3.60/1.01      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_505,plain,
% 3.60/1.01      ( v1_relat_1(X0) != iProver_top
% 3.60/1.01      | v1_relat_1(X1) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_16,negated_conjecture,
% 3.60/1.01      ( v1_relat_1(sK0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_501,plain,
% 3.60/1.01      ( v1_relat_1(sK0) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_13,plain,
% 3.60/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.60/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_12,plain,
% 3.60/1.01      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.60/1.01      | ~ v1_relat_1(X1)
% 3.60/1.01      | ~ v1_relat_1(X0)
% 3.60/1.01      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_502,plain,
% 3.60/1.01      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 3.60/1.01      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.60/1.01      | v1_relat_1(X1) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_768,plain,
% 3.60/1.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 3.60/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_13,c_502]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_14,plain,
% 3.60/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.60/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_782,plain,
% 3.60/1.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.60/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_768,c_14]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8,plain,
% 3.60/1.01      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_30,plain,
% 3.60/1.01      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_32,plain,
% 3.60/1.01      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.60/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_0,plain,
% 3.60/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_48,plain,
% 3.60/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1600,plain,
% 3.60/1.01      ( v1_relat_1(X0) != iProver_top
% 3.60/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.60/1.01      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_782,c_32,c_48]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1601,plain,
% 3.60/1.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.60/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.60/1.01      inference(renaming,[status(thm)],[c_1600]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5,plain,
% 3.60/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_509,plain,
% 3.60/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1607,plain,
% 3.60/1.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.60/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.60/1.01      inference(forward_subsumption_resolution,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1601,c_509]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1612,plain,
% 3.60/1.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_501,c_1607]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_10,plain,
% 3.60/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 3.60/1.01      | ~ v1_relat_1(X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_504,plain,
% 3.60/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1642,plain,
% 3.60/1.01      ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) = iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1612,c_504]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_513,plain,
% 3.60/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_7,plain,
% 3.60/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_507,plain,
% 3.60/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.60/1.01      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1,plain,
% 3.60/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.60/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_512,plain,
% 3.60/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_865,plain,
% 3.60/1.01      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.60/1.01      | v1_xboole_0(X0) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_507,c_512]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1099,plain,
% 3.60/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_513,c_865]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1654,plain,
% 3.60/1.01      ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) = iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 3.60/1.01      inference(demodulation,[status(thm)],[c_1642,c_1099]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2,plain,
% 3.60/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.60/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_511,plain,
% 3.60/1.01      ( X0 = X1
% 3.60/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.60/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1823,plain,
% 3.60/1.01      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 3.60/1.01      | r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1654,c_511]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1941,plain,
% 3.60/1.01      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 3.60/1.01      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 3.60/1.01      inference(forward_subsumption_resolution,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1823,c_509]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1943,plain,
% 3.60/1.01      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 3.60/1.01      | v1_relat_1(sK0) != iProver_top
% 3.60/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_505,c_1941]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_17,plain,
% 3.60/1.01      ( v1_relat_1(sK0) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3047,plain,
% 3.60/1.01      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_1943,c_17,c_32,c_48]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_15,negated_conjecture,
% 3.60/1.01      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.60/1.01      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3061,plain,
% 3.60/1.01      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 3.60/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/1.01      inference(demodulation,[status(thm)],[c_3047,c_15]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3062,plain,
% 3.60/1.01      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_3061]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2784,plain,
% 3.60/1.01      ( r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_254,plain,
% 3.60/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.60/1.01      theory(equality) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2725,plain,
% 3.60/1.01      ( ~ v1_xboole_0(X0)
% 3.60/1.01      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_254]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2727,plain,
% 3.60/1.01      ( v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 3.60/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_2725]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2427,plain,
% 3.60/1.01      ( ~ r1_tarski(X0,k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 3.60/1.01      | ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),X0)
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = X0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2429,plain,
% 3.60/1.01      ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)
% 3.60/1.01      | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 3.60/1.01      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_2427]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_252,plain,( X0 = X0 ),theory(equality) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1853,plain,
% 3.60/1.01      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_252]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_6,plain,
% 3.60/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1589,plain,
% 3.60/1.01      ( v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
% 3.60/1.01      | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1120,plain,
% 3.60/1.01      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
% 3.60/1.01      | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_629,plain,
% 3.60/1.01      ( ~ r1_tarski(X0,X1)
% 3.60/1.01      | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
% 3.60/1.01      | k5_relat_1(sK0,k1_xboole_0) != X0
% 3.60/1.01      | k1_xboole_0 != X1 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_255]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_755,plain,
% 3.60/1.01      ( ~ r1_tarski(k5_relat_1(sK0,X0),X1)
% 3.60/1.01      | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
% 3.60/1.01      | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,X0)
% 3.60/1.01      | k1_xboole_0 != X1 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_629]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_901,plain,
% 3.60/1.01      ( ~ r1_tarski(k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))
% 3.60/1.01      | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
% 3.60/1.01      | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,X0)
% 3.60/1.01      | k1_xboole_0 != k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_755]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_904,plain,
% 3.60/1.01      ( ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
% 3.60/1.01      | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
% 3.60/1.01      | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
% 3.60/1.01      | k1_xboole_0 != k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_901]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_744,plain,
% 3.60/1.01      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 3.60/1.01      | ~ v1_relat_1(sK0)
% 3.60/1.01      | ~ v1_relat_1(k1_xboole_0) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_716,plain,
% 3.60/1.01      ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
% 3.60/1.01      | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_661,plain,
% 3.60/1.01      ( r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0)) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4,plain,
% 3.60/1.01      ( r1_tarski(X0,X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_655,plain,
% 3.60/1.01      ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0)) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_634,plain,
% 3.60/1.01      ( ~ r1_tarski(X0,k5_relat_1(sK0,k1_xboole_0))
% 3.60/1.01      | ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),X0)
% 3.60/1.01      | k5_relat_1(sK0,k1_xboole_0) = X0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_654,plain,
% 3.60/1.01      ( ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0))
% 3.60/1.01      | k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_634]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_636,plain,
% 3.60/1.01      ( ~ r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
% 3.60/1.01      | ~ r1_tarski(k1_xboole_0,k5_relat_1(sK0,k1_xboole_0))
% 3.60/1.01      | k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_634]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_43,plain,
% 3.60/1.01      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.60/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_38,plain,
% 3.60/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_31,plain,
% 3.60/1.01      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(contradiction,plain,
% 3.60/1.01      ( $false ),
% 3.60/1.01      inference(minisat,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_13331,c_8917,c_3951,c_3062,c_2784,c_2727,c_2429,
% 3.60/1.01                 c_1853,c_1589,c_1120,c_904,c_744,c_716,c_661,c_655,
% 3.60/1.01                 c_654,c_636,c_0,c_43,c_38,c_31,c_13,c_16]) ).
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  ------                               Statistics
% 3.60/1.01  
% 3.60/1.01  ------ General
% 3.60/1.01  
% 3.60/1.01  abstr_ref_over_cycles:                  0
% 3.60/1.01  abstr_ref_under_cycles:                 0
% 3.60/1.01  gc_basic_clause_elim:                   0
% 3.60/1.01  forced_gc_time:                         0
% 3.60/1.01  parsing_time:                           0.01
% 3.60/1.01  unif_index_cands_time:                  0.
% 3.60/1.01  unif_index_add_time:                    0.
% 3.60/1.01  orderings_time:                         0.
% 3.60/1.01  out_proof_time:                         0.012
% 3.60/1.01  total_time:                             0.396
% 3.60/1.01  num_of_symbols:                         40
% 3.60/1.01  num_of_terms:                           7906
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing
% 3.60/1.01  
% 3.60/1.01  num_of_splits:                          0
% 3.60/1.01  num_of_split_atoms:                     0
% 3.60/1.01  num_of_reused_defs:                     0
% 3.60/1.01  num_eq_ax_congr_red:                    0
% 3.60/1.01  num_of_sem_filtered_clauses:            1
% 3.60/1.01  num_of_subtypes:                        0
% 3.60/1.01  monotx_restored_types:                  0
% 3.60/1.01  sat_num_of_epr_types:                   0
% 3.60/1.01  sat_num_of_non_cyclic_types:            0
% 3.60/1.01  sat_guarded_non_collapsed_types:        0
% 3.60/1.01  num_pure_diseq_elim:                    0
% 3.60/1.01  simp_replaced_by:                       0
% 3.60/1.01  res_preprocessed:                       83
% 3.60/1.01  prep_upred:                             0
% 3.60/1.01  prep_unflattend:                        0
% 3.60/1.01  smt_new_axioms:                         0
% 3.60/1.01  pred_elim_cands:                        3
% 3.60/1.01  pred_elim:                              0
% 3.60/1.01  pred_elim_cl:                           0
% 3.60/1.01  pred_elim_cycles:                       2
% 3.60/1.01  merged_defs:                            0
% 3.60/1.01  merged_defs_ncl:                        0
% 3.60/1.01  bin_hyper_res:                          0
% 3.60/1.01  prep_cycles:                            4
% 3.60/1.01  pred_elim_time:                         0.
% 3.60/1.01  splitting_time:                         0.
% 3.60/1.01  sem_filter_time:                        0.
% 3.60/1.01  monotx_time:                            0.
% 3.60/1.01  subtype_inf_time:                       0.
% 3.60/1.01  
% 3.60/1.01  ------ Problem properties
% 3.60/1.01  
% 3.60/1.01  clauses:                                16
% 3.60/1.01  conjectures:                            2
% 3.60/1.01  epr:                                    7
% 3.60/1.01  horn:                                   16
% 3.60/1.01  ground:                                 5
% 3.60/1.01  unary:                                  6
% 3.60/1.01  binary:                                 6
% 3.60/1.01  lits:                                   31
% 3.60/1.01  lits_eq:                                7
% 3.60/1.01  fd_pure:                                0
% 3.60/1.01  fd_pseudo:                              0
% 3.60/1.01  fd_cond:                                1
% 3.60/1.01  fd_pseudo_cond:                         1
% 3.60/1.01  ac_symbols:                             0
% 3.60/1.01  
% 3.60/1.01  ------ Propositional Solver
% 3.60/1.01  
% 3.60/1.01  prop_solver_calls:                      33
% 3.60/1.01  prop_fast_solver_calls:                 730
% 3.60/1.01  smt_solver_calls:                       0
% 3.60/1.01  smt_fast_solver_calls:                  0
% 3.60/1.01  prop_num_of_clauses:                    3513
% 3.60/1.01  prop_preprocess_simplified:             8892
% 3.60/1.01  prop_fo_subsumed:                       18
% 3.60/1.01  prop_solver_time:                       0.
% 3.60/1.01  smt_solver_time:                        0.
% 3.60/1.01  smt_fast_solver_time:                   0.
% 3.60/1.01  prop_fast_solver_time:                  0.
% 3.60/1.01  prop_unsat_core_time:                   0.
% 3.60/1.01  
% 3.60/1.01  ------ QBF
% 3.60/1.01  
% 3.60/1.01  qbf_q_res:                              0
% 3.60/1.01  qbf_num_tautologies:                    0
% 3.60/1.01  qbf_prep_cycles:                        0
% 3.60/1.01  
% 3.60/1.01  ------ BMC1
% 3.60/1.01  
% 3.60/1.01  bmc1_current_bound:                     -1
% 3.60/1.01  bmc1_last_solved_bound:                 -1
% 3.60/1.01  bmc1_unsat_core_size:                   -1
% 3.60/1.01  bmc1_unsat_core_parents_size:           -1
% 3.60/1.01  bmc1_merge_next_fun:                    0
% 3.60/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.60/1.01  
% 3.60/1.01  ------ Instantiation
% 3.60/1.01  
% 3.60/1.01  inst_num_of_clauses:                    1106
% 3.60/1.01  inst_num_in_passive:                    237
% 3.60/1.01  inst_num_in_active:                     687
% 3.60/1.01  inst_num_in_unprocessed:                181
% 3.60/1.01  inst_num_of_loops:                      771
% 3.60/1.01  inst_num_of_learning_restarts:          0
% 3.60/1.01  inst_num_moves_active_passive:          76
% 3.60/1.01  inst_lit_activity:                      0
% 3.60/1.01  inst_lit_activity_moves:                0
% 3.60/1.01  inst_num_tautologies:                   0
% 3.60/1.01  inst_num_prop_implied:                  0
% 3.60/1.01  inst_num_existing_simplified:           0
% 3.60/1.01  inst_num_eq_res_simplified:             0
% 3.60/1.01  inst_num_child_elim:                    0
% 3.60/1.01  inst_num_of_dismatching_blockings:      553
% 3.60/1.01  inst_num_of_non_proper_insts:           2293
% 3.60/1.01  inst_num_of_duplicates:                 0
% 3.60/1.01  inst_inst_num_from_inst_to_res:         0
% 3.60/1.01  inst_dismatching_checking_time:         0.
% 3.60/1.01  
% 3.60/1.01  ------ Resolution
% 3.60/1.01  
% 3.60/1.01  res_num_of_clauses:                     0
% 3.60/1.01  res_num_in_passive:                     0
% 3.60/1.01  res_num_in_active:                      0
% 3.60/1.01  res_num_of_loops:                       87
% 3.60/1.01  res_forward_subset_subsumed:            330
% 3.60/1.01  res_backward_subset_subsumed:           0
% 3.60/1.01  res_forward_subsumed:                   0
% 3.60/1.01  res_backward_subsumed:                  0
% 3.60/1.01  res_forward_subsumption_resolution:     0
% 3.60/1.01  res_backward_subsumption_resolution:    0
% 3.60/1.01  res_clause_to_clause_subsumption:       3348
% 3.60/1.01  res_orphan_elimination:                 0
% 3.60/1.01  res_tautology_del:                      278
% 3.60/1.01  res_num_eq_res_simplified:              0
% 3.60/1.01  res_num_sel_changes:                    0
% 3.60/1.01  res_moves_from_active_to_pass:          0
% 3.60/1.01  
% 3.60/1.01  ------ Superposition
% 3.60/1.01  
% 3.60/1.01  sup_time_total:                         0.
% 3.60/1.01  sup_time_generating:                    0.
% 3.60/1.01  sup_time_sim_full:                      0.
% 3.60/1.01  sup_time_sim_immed:                     0.
% 3.60/1.01  
% 3.60/1.01  sup_num_of_clauses:                     331
% 3.60/1.01  sup_num_in_active:                      138
% 3.60/1.01  sup_num_in_passive:                     193
% 3.60/1.01  sup_num_of_loops:                       154
% 3.60/1.01  sup_fw_superposition:                   363
% 3.60/1.01  sup_bw_superposition:                   65
% 3.60/1.01  sup_immediate_simplified:               117
% 3.60/1.01  sup_given_eliminated:                   0
% 3.60/1.01  comparisons_done:                       0
% 3.60/1.01  comparisons_avoided:                    0
% 3.60/1.01  
% 3.60/1.01  ------ Simplifications
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  sim_fw_subset_subsumed:                 4
% 3.60/1.01  sim_bw_subset_subsumed:                 6
% 3.60/1.01  sim_fw_subsumed:                        6
% 3.60/1.01  sim_bw_subsumed:                        0
% 3.60/1.01  sim_fw_subsumption_res:                 3
% 3.60/1.01  sim_bw_subsumption_res:                 0
% 3.60/1.01  sim_tautology_del:                      3
% 3.60/1.01  sim_eq_tautology_del:                   36
% 3.60/1.01  sim_eq_res_simp:                        1
% 3.60/1.01  sim_fw_demodulated:                     50
% 3.60/1.01  sim_bw_demodulated:                     13
% 3.60/1.01  sim_light_normalised:                   78
% 3.60/1.01  sim_joinable_taut:                      0
% 3.60/1.01  sim_joinable_simp:                      0
% 3.60/1.01  sim_ac_normalised:                      0
% 3.60/1.01  sim_smt_subsumption:                    0
% 3.60/1.01  
%------------------------------------------------------------------------------
