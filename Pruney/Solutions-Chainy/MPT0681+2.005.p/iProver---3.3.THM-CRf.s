%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:20 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 274 expanded)
%              Number of clauses        :   62 ( 121 expanded)
%              Number of leaves         :   16 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  233 ( 837 expanded)
%              Number of equality atoms :  113 ( 228 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f30,f30])).

fof(f42,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_333,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_337,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1884,plain,
    ( X0 != X1
    | X2 != k2_relat_1(X1)
    | k2_relat_1(X0) = X2 ),
    inference(resolution,[status(thm)],[c_333,c_337])).

cnf(c_332,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1883,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_333,c_332])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_222,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_223,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_3220,plain,
    ( k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[status(thm)],[c_1883,c_223])).

cnf(c_7851,plain,
    ( X0 != k7_relat_1(sK2,X1)
    | k2_relat_1(X0) = k9_relat_1(sK2,X1) ),
    inference(resolution,[status(thm)],[c_1884,c_3220])).

cnf(c_1890,plain,
    ( X0 != k9_relat_1(sK2,X1)
    | k2_relat_1(k7_relat_1(sK2,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_333,c_223])).

cnf(c_1994,plain,
    ( X0 != X1
    | X1 != k9_relat_1(sK2,X2)
    | k2_relat_1(k7_relat_1(sK2,X2)) = X0 ),
    inference(resolution,[status(thm)],[c_1890,c_333])).

cnf(c_8964,plain,
    ( X0 != k7_relat_1(sK2,X1)
    | X2 != k2_relat_1(X0)
    | k2_relat_1(k7_relat_1(sK2,X1)) = X2 ),
    inference(resolution,[status(thm)],[c_7851,c_1994])).

cnf(c_8965,plain,
    ( k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8964])).

cnf(c_3556,plain,
    ( X0 != k2_relat_1(k7_relat_1(sK2,X1))
    | k9_relat_1(sK2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3220,c_333])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_210,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | k7_relat_1(X1,X0) = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_211,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
    | k7_relat_1(sK2,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_1888,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
    | X1 != k1_xboole_0
    | k7_relat_1(sK2,X0) = X1 ),
    inference(resolution,[status(thm)],[c_333,c_211])).

cnf(c_3808,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
    | k9_relat_1(sK2,X1) = k7_relat_1(sK2,X0)
    | k2_relat_1(k7_relat_1(sK2,X1)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3556,c_1888])).

cnf(c_5696,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
    | k7_relat_1(sK2,X0) = k9_relat_1(sK2,X1)
    | k2_relat_1(k7_relat_1(sK2,X1)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3808,c_1883])).

cnf(c_5698,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2))
    | k7_relat_1(sK2,k1_xboole_0) = k9_relat_1(sK2,k1_xboole_0)
    | k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5696])).

cnf(c_3216,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
    | k1_xboole_0 = k7_relat_1(sK2,X0) ),
    inference(resolution,[status(thm)],[c_1883,c_211])).

cnf(c_3577,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
    | X1 != k7_relat_1(sK2,X0)
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_3216,c_333])).

cnf(c_4094,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
    | k7_relat_1(sK2,X0) != k9_relat_1(sK2,X1)
    | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,X1)) ),
    inference(resolution,[status(thm)],[c_3577,c_1890])).

cnf(c_4096,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2))
    | k7_relat_1(sK2,k1_xboole_0) != k9_relat_1(sK2,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4094])).

cnf(c_3557,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3556])).

cnf(c_3218,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2))
    | k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3216])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3207,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1883,c_10])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_597,plain,
    ( r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_602,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1066,plain,
    ( r1_xboole_0(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_597,c_602])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_599,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1215,plain,
    ( k4_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_1066,c_599])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_198,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_199,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_203,plain,
    ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_17,c_16])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_604,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1944,plain,
    ( k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != k1_xboole_0
    | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_203,c_604])).

cnf(c_2369,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK1,sK1)) != k1_xboole_0
    | r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1944])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_615,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_2372,plain,
    ( k9_relat_1(sK2,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2369,c_615])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_796,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_680,plain,
    ( r1_xboole_0(X0,k1_relat_1(sK2))
    | ~ r1_xboole_0(k1_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_682,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_677,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0))
    | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_678,plain,
    ( r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,plain,
    ( r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8965,c_5698,c_4096,c_3557,c_3218,c_3207,c_2372,c_796,c_682,c_678,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:07:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.88/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.01  
% 2.88/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/1.01  
% 2.88/1.01  ------  iProver source info
% 2.88/1.01  
% 2.88/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.88/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/1.01  git: non_committed_changes: false
% 2.88/1.01  git: last_make_outside_of_git: false
% 2.88/1.01  
% 2.88/1.01  ------ 
% 2.88/1.01  ------ Parsing...
% 2.88/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/1.01  
% 2.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.88/1.01  
% 2.88/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/1.01  
% 2.88/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/1.01  ------ Proving...
% 2.88/1.01  ------ Problem Properties 
% 2.88/1.01  
% 2.88/1.01  
% 2.88/1.01  clauses                                 15
% 2.88/1.01  conjectures                             2
% 2.88/1.01  EPR                                     3
% 2.88/1.01  Horn                                    15
% 2.88/1.01  unary                                   9
% 2.88/1.01  binary                                  6
% 2.88/1.01  lits                                    21
% 2.88/1.01  lits eq                                 11
% 2.88/1.01  fd_pure                                 0
% 2.88/1.01  fd_pseudo                               0
% 2.88/1.01  fd_cond                                 0
% 2.88/1.01  fd_pseudo_cond                          0
% 2.88/1.01  AC symbols                              0
% 2.88/1.01  
% 2.88/1.01  ------ Input Options Time Limit: Unbounded
% 2.88/1.01  
% 2.88/1.01  
% 2.88/1.01  ------ 
% 2.88/1.01  Current options:
% 2.88/1.01  ------ 
% 2.88/1.01  
% 2.88/1.01  
% 2.88/1.01  
% 2.88/1.01  
% 2.88/1.01  ------ Proving...
% 2.88/1.01  
% 2.88/1.01  
% 2.88/1.01  % SZS status Theorem for theBenchmark.p
% 2.88/1.01  
% 2.88/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/1.01  
% 2.88/1.01  fof(f8,axiom,(
% 2.88/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f15,plain,(
% 2.88/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.88/1.01    inference(ennf_transformation,[],[f8])).
% 2.88/1.01  
% 2.88/1.01  fof(f34,plain,(
% 2.88/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.88/1.01    inference(cnf_transformation,[],[f15])).
% 2.88/1.01  
% 2.88/1.01  fof(f12,conjecture,(
% 2.88/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f13,negated_conjecture,(
% 2.88/1.01    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.88/1.01    inference(negated_conjecture,[],[f12])).
% 2.88/1.01  
% 2.88/1.01  fof(f19,plain,(
% 2.88/1.01    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.88/1.01    inference(ennf_transformation,[],[f13])).
% 2.88/1.01  
% 2.88/1.01  fof(f20,plain,(
% 2.88/1.01    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.88/1.01    inference(flattening,[],[f19])).
% 2.88/1.01  
% 2.88/1.01  fof(f23,plain,(
% 2.88/1.01    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.88/1.01    introduced(choice_axiom,[])).
% 2.88/1.01  
% 2.88/1.01  fof(f24,plain,(
% 2.88/1.01    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.88/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 2.88/1.01  
% 2.88/1.01  fof(f39,plain,(
% 2.88/1.01    v1_relat_1(sK2)),
% 2.88/1.01    inference(cnf_transformation,[],[f24])).
% 2.88/1.01  
% 2.88/1.01  fof(f9,axiom,(
% 2.88/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f16,plain,(
% 2.88/1.01    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.88/1.01    inference(ennf_transformation,[],[f9])).
% 2.88/1.01  
% 2.88/1.01  fof(f35,plain,(
% 2.88/1.01    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.88/1.01    inference(cnf_transformation,[],[f16])).
% 2.88/1.01  
% 2.88/1.01  fof(f10,axiom,(
% 2.88/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f37,plain,(
% 2.88/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.88/1.01    inference(cnf_transformation,[],[f10])).
% 2.88/1.01  
% 2.88/1.01  fof(f41,plain,(
% 2.88/1.01    r1_xboole_0(sK0,sK1)),
% 2.88/1.01    inference(cnf_transformation,[],[f24])).
% 2.88/1.01  
% 2.88/1.01  fof(f2,axiom,(
% 2.88/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f14,plain,(
% 2.88/1.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.88/1.01    inference(ennf_transformation,[],[f2])).
% 2.88/1.01  
% 2.88/1.01  fof(f27,plain,(
% 2.88/1.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.88/1.01    inference(cnf_transformation,[],[f14])).
% 2.88/1.01  
% 2.88/1.01  fof(f7,axiom,(
% 2.88/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f22,plain,(
% 2.88/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.88/1.01    inference(nnf_transformation,[],[f7])).
% 2.88/1.01  
% 2.88/1.01  fof(f32,plain,(
% 2.88/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.88/1.01    inference(cnf_transformation,[],[f22])).
% 2.88/1.01  
% 2.88/1.01  fof(f11,axiom,(
% 2.88/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f17,plain,(
% 2.88/1.01    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.88/1.01    inference(ennf_transformation,[],[f11])).
% 2.88/1.01  
% 2.88/1.01  fof(f18,plain,(
% 2.88/1.01    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.88/1.01    inference(flattening,[],[f17])).
% 2.88/1.01  
% 2.88/1.01  fof(f38,plain,(
% 2.88/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.88/1.01    inference(cnf_transformation,[],[f18])).
% 2.88/1.01  
% 2.88/1.01  fof(f5,axiom,(
% 2.88/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f30,plain,(
% 2.88/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.88/1.01    inference(cnf_transformation,[],[f5])).
% 2.88/1.01  
% 2.88/1.01  fof(f47,plain,(
% 2.88/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.88/1.01    inference(definition_unfolding,[],[f38,f30,f30])).
% 2.88/1.01  
% 2.88/1.01  fof(f42,plain,(
% 2.88/1.01    v2_funct_1(sK2)),
% 2.88/1.01    inference(cnf_transformation,[],[f24])).
% 2.88/1.01  
% 2.88/1.01  fof(f40,plain,(
% 2.88/1.01    v1_funct_1(sK2)),
% 2.88/1.01    inference(cnf_transformation,[],[f24])).
% 2.88/1.01  
% 2.88/1.01  fof(f1,axiom,(
% 2.88/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f21,plain,(
% 2.88/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.88/1.01    inference(nnf_transformation,[],[f1])).
% 2.88/1.01  
% 2.88/1.01  fof(f26,plain,(
% 2.88/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.88/1.01    inference(cnf_transformation,[],[f21])).
% 2.88/1.01  
% 2.88/1.01  fof(f44,plain,(
% 2.88/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.88/1.01    inference(definition_unfolding,[],[f26,f30])).
% 2.88/1.01  
% 2.88/1.01  fof(f3,axiom,(
% 2.88/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f28,plain,(
% 2.88/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.88/1.01    inference(cnf_transformation,[],[f3])).
% 2.88/1.01  
% 2.88/1.01  fof(f46,plain,(
% 2.88/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.88/1.01    inference(definition_unfolding,[],[f28,f30])).
% 2.88/1.01  
% 2.88/1.01  fof(f4,axiom,(
% 2.88/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f29,plain,(
% 2.88/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.88/1.01    inference(cnf_transformation,[],[f4])).
% 2.88/1.01  
% 2.88/1.01  fof(f6,axiom,(
% 2.88/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.88/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.01  
% 2.88/1.01  fof(f31,plain,(
% 2.88/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.88/1.01    inference(cnf_transformation,[],[f6])).
% 2.88/1.01  
% 2.88/1.01  fof(f43,plain,(
% 2.88/1.01    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.88/1.01    inference(cnf_transformation,[],[f24])).
% 2.88/1.01  
% 2.88/1.01  cnf(c_333,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_337,plain,
% 2.88/1.01      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 2.88/1.01      theory(equality) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1884,plain,
% 2.88/1.01      ( X0 != X1 | X2 != k2_relat_1(X1) | k2_relat_1(X0) = X2 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_333,c_337]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_332,plain,( X0 = X0 ),theory(equality) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1883,plain,
% 2.88/1.01      ( X0 != X1 | X1 = X0 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_333,c_332]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_8,plain,
% 2.88/1.01      ( ~ v1_relat_1(X0)
% 2.88/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.88/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_17,negated_conjecture,
% 2.88/1.01      ( v1_relat_1(sK2) ),
% 2.88/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_222,plain,
% 2.88/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | sK2 != X0 ),
% 2.88/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_223,plain,
% 2.88/1.01      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 2.88/1.01      inference(unflattening,[status(thm)],[c_222]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3220,plain,
% 2.88/1.01      ( k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_1883,c_223]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_7851,plain,
% 2.88/1.01      ( X0 != k7_relat_1(sK2,X1) | k2_relat_1(X0) = k9_relat_1(sK2,X1) ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_1884,c_3220]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1890,plain,
% 2.88/1.01      ( X0 != k9_relat_1(sK2,X1) | k2_relat_1(k7_relat_1(sK2,X1)) = X0 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_333,c_223]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1994,plain,
% 2.88/1.01      ( X0 != X1
% 2.88/1.01      | X1 != k9_relat_1(sK2,X2)
% 2.88/1.01      | k2_relat_1(k7_relat_1(sK2,X2)) = X0 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_1890,c_333]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_8964,plain,
% 2.88/1.01      ( X0 != k7_relat_1(sK2,X1)
% 2.88/1.01      | X2 != k2_relat_1(X0)
% 2.88/1.01      | k2_relat_1(k7_relat_1(sK2,X1)) = X2 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_7851,c_1994]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_8965,plain,
% 2.88/1.01      ( k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
% 2.88/1.01      | k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
% 2.88/1.01      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_8964]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3556,plain,
% 2.88/1.01      ( X0 != k2_relat_1(k7_relat_1(sK2,X1)) | k9_relat_1(sK2,X1) = X0 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_3220,c_333]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_9,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 2.88/1.01      | ~ v1_relat_1(X1)
% 2.88/1.01      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 2.88/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_210,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 2.88/1.01      | k7_relat_1(X1,X0) = k1_xboole_0
% 2.88/1.01      | sK2 != X1 ),
% 2.88/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_211,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | k7_relat_1(sK2,X0) = k1_xboole_0 ),
% 2.88/1.01      inference(unflattening,[status(thm)],[c_210]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1888,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | X1 != k1_xboole_0
% 2.88/1.01      | k7_relat_1(sK2,X0) = X1 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_333,c_211]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3808,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | k9_relat_1(sK2,X1) = k7_relat_1(sK2,X0)
% 2.88/1.01      | k2_relat_1(k7_relat_1(sK2,X1)) != k1_xboole_0 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_3556,c_1888]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_5696,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | k7_relat_1(sK2,X0) = k9_relat_1(sK2,X1)
% 2.88/1.01      | k2_relat_1(k7_relat_1(sK2,X1)) != k1_xboole_0 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_3808,c_1883]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_5698,plain,
% 2.88/1.01      ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2))
% 2.88/1.01      | k7_relat_1(sK2,k1_xboole_0) = k9_relat_1(sK2,k1_xboole_0)
% 2.88/1.01      | k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) != k1_xboole_0 ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_5696]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3216,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | k1_xboole_0 = k7_relat_1(sK2,X0) ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_1883,c_211]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3577,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | X1 != k7_relat_1(sK2,X0)
% 2.88/1.01      | k1_xboole_0 = X1 ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_3216,c_333]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_4094,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | k7_relat_1(sK2,X0) != k9_relat_1(sK2,X1)
% 2.88/1.01      | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,X1)) ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_3577,c_1890]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_4096,plain,
% 2.88/1.01      ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2))
% 2.88/1.01      | k7_relat_1(sK2,k1_xboole_0) != k9_relat_1(sK2,k1_xboole_0)
% 2.88/1.01      | k1_xboole_0 = k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_4094]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3557,plain,
% 2.88/1.01      ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0
% 2.88/1.01      | k1_xboole_0 != k2_relat_1(k7_relat_1(sK2,k1_xboole_0)) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_3556]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3218,plain,
% 2.88/1.01      ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK2))
% 2.88/1.01      | k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_3216]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_10,plain,
% 2.88/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.88/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3207,plain,
% 2.88/1.01      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.88/1.01      inference(resolution,[status(thm)],[c_1883,c_10]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_15,negated_conjecture,
% 2.88/1.01      ( r1_xboole_0(sK0,sK1) ),
% 2.88/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_597,plain,
% 2.88/1.01      ( r1_xboole_0(sK0,sK1) = iProver_top ),
% 2.88/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_2,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.88/1.01      inference(cnf_transformation,[],[f27]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_602,plain,
% 2.88/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 2.88/1.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.88/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1066,plain,
% 2.88/1.01      ( r1_xboole_0(sK1,sK0) = iProver_top ),
% 2.88/1.01      inference(superposition,[status(thm)],[c_597,c_602]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_7,plain,
% 2.88/1.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.88/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_599,plain,
% 2.88/1.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.88/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1215,plain,
% 2.88/1.01      ( k4_xboole_0(sK1,sK0) = sK1 ),
% 2.88/1.01      inference(superposition,[status(thm)],[c_1066,c_599]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_12,plain,
% 2.88/1.01      ( ~ v1_funct_1(X0)
% 2.88/1.01      | ~ v2_funct_1(X0)
% 2.88/1.01      | ~ v1_relat_1(X0)
% 2.88/1.01      | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 2.88/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_14,negated_conjecture,
% 2.88/1.01      ( v2_funct_1(sK2) ),
% 2.88/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_198,plain,
% 2.88/1.01      ( ~ v1_funct_1(X0)
% 2.88/1.01      | ~ v1_relat_1(X0)
% 2.88/1.01      | k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 2.88/1.01      | sK2 != X0 ),
% 2.88/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_199,plain,
% 2.88/1.01      ( ~ v1_funct_1(sK2)
% 2.88/1.01      | ~ v1_relat_1(sK2)
% 2.88/1.01      | k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 2.88/1.01      inference(unflattening,[status(thm)],[c_198]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_16,negated_conjecture,
% 2.88/1.01      ( v1_funct_1(sK2) ),
% 2.88/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_203,plain,
% 2.88/1.01      ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 2.88/1.01      inference(global_propositional_subsumption,
% 2.88/1.01                [status(thm)],
% 2.88/1.01                [c_199,c_17,c_16]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_0,plain,
% 2.88/1.01      ( r1_xboole_0(X0,X1)
% 2.88/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.88/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_604,plain,
% 2.88/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 2.88/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.88/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_1944,plain,
% 2.88/1.01      ( k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != k1_xboole_0
% 2.88/1.01      | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top ),
% 2.88/1.01      inference(superposition,[status(thm)],[c_203,c_604]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_2369,plain,
% 2.88/1.01      ( k9_relat_1(sK2,k4_xboole_0(sK1,sK1)) != k1_xboole_0
% 2.88/1.01      | r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0)) = iProver_top ),
% 2.88/1.01      inference(superposition,[status(thm)],[c_1215,c_1944]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_3,plain,
% 2.88/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.88/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_4,plain,
% 2.88/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.88/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_615,plain,
% 2.88/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.88/1.01      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_2372,plain,
% 2.88/1.01      ( k9_relat_1(sK2,k1_xboole_0) != k1_xboole_0
% 2.88/1.01      | r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0)) = iProver_top ),
% 2.88/1.01      inference(demodulation,[status(thm)],[c_2369,c_615]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_5,plain,
% 2.88/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.88/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_796,plain,
% 2.88/1.01      ( r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_680,plain,
% 2.88/1.01      ( r1_xboole_0(X0,k1_relat_1(sK2))
% 2.88/1.01      | ~ r1_xboole_0(k1_relat_1(sK2),X0) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_682,plain,
% 2.88/1.01      ( ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
% 2.88/1.01      | r1_xboole_0(k1_xboole_0,k1_relat_1(sK2)) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_680]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_677,plain,
% 2.88/1.01      ( ~ r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0))
% 2.88/1.01      | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 2.88/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_678,plain,
% 2.88/1.01      ( r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0)) != iProver_top
% 2.88/1.01      | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 2.88/1.01      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_13,negated_conjecture,
% 2.88/1.01      ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 2.88/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(c_22,plain,
% 2.88/1.01      ( r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != iProver_top ),
% 2.88/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.88/1.01  
% 2.88/1.01  cnf(contradiction,plain,
% 2.88/1.01      ( $false ),
% 2.88/1.01      inference(minisat,
% 2.88/1.01                [status(thm)],
% 2.88/1.01                [c_8965,c_5698,c_4096,c_3557,c_3218,c_3207,c_2372,c_796,
% 2.88/1.01                 c_682,c_678,c_22]) ).
% 2.88/1.01  
% 2.88/1.01  
% 2.88/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/1.01  
% 2.88/1.01  ------                               Statistics
% 2.88/1.01  
% 2.88/1.01  ------ Selected
% 2.88/1.01  
% 2.88/1.01  total_time:                             0.309
% 2.88/1.01  
%------------------------------------------------------------------------------
