%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:43 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 120 expanded)
%              Number of clauses        :   52 (  58 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 ( 293 expanded)
%              Number of equality atoms :  109 ( 150 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f34,f34])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f40,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_450,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_xboole_0(X1,X2))
    | X0 = k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_542,plain,
    ( ~ v1_xboole_0(k4_xboole_0(X0,X1))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_450])).

cnf(c_31260,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_216,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_10200,plain,
    ( X0 != k4_xboole_0(sK0,k1_relat_1(sK1))
    | X1 != sK0
    | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_31257,plain,
    ( X0 != sK0
    | k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_xboole_0 != k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_10200])).

cnf(c_31261,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | sK0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_31257])).

cnf(c_215,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_517,plain,
    ( X0 != X1
    | k1_relat_1(k7_relat_1(sK1,sK0)) != X1
    | k1_relat_1(k7_relat_1(sK1,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_3744,plain,
    ( X0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = X0
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_10199,plain,
    ( k4_xboole_0(X0,X1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(X0,X1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_3744])).

cnf(c_30842,plain,
    ( k4_xboole_0(X0,k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(X0,k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_10199])).

cnf(c_30844,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_30842])).

cnf(c_469,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != X0
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_3049,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(X0,k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | sK0 != k4_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_3050,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3049])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1575,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_865,plain,
    ( X0 != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = X0
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1574,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_801,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_1426,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X1,k1_xboole_0)
    | k4_xboole_0(X1,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1427,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) != sK0
    | sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_689,plain,
    ( X0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = X0
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_851,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
    | k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_635,plain,
    ( r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(X0,sK0) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_141,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X2 != X1
    | k4_xboole_0(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_142,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | v1_xboole_0(k4_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_141])).

cnf(c_645,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,k1_relat_1(sK1)),sK0)
    | v1_xboole_0(k4_xboole_0(X0,k1_relat_1(sK1))) ),
    inference(resolution,[status(thm)],[c_635,c_142])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_779,plain,
    ( v1_xboole_0(k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[status(thm)],[c_645,c_6])).

cnf(c_214,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_516,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_134,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_135,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_134])).

cnf(c_136,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_39,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_35,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_29,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12,negated_conjecture,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31260,c_31261,c_30844,c_3050,c_1575,c_1574,c_1427,c_851,c_779,c_516,c_136,c_1,c_39,c_35,c_29,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:30:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.84/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.52  
% 7.84/1.52  ------  iProver source info
% 7.84/1.52  
% 7.84/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.52  git: non_committed_changes: false
% 7.84/1.52  git: last_make_outside_of_git: false
% 7.84/1.52  
% 7.84/1.52  ------ 
% 7.84/1.52  ------ Parsing...
% 7.84/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.52  
% 7.84/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.84/1.52  
% 7.84/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.52  
% 7.84/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.52  ------ Proving...
% 7.84/1.52  ------ Problem Properties 
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  clauses                                 12
% 7.84/1.52  conjectures                             2
% 7.84/1.52  EPR                                     5
% 7.84/1.52  Horn                                    12
% 7.84/1.52  unary                                   8
% 7.84/1.52  binary                                  1
% 7.84/1.52  lits                                    19
% 7.84/1.52  lits eq                                 6
% 7.84/1.52  fd_pure                                 0
% 7.84/1.52  fd_pseudo                               0
% 7.84/1.52  fd_cond                                 0
% 7.84/1.52  fd_pseudo_cond                          2
% 7.84/1.52  AC symbols                              0
% 7.84/1.52  
% 7.84/1.52  ------ Input Options Time Limit: Unbounded
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  ------ 
% 7.84/1.52  Current options:
% 7.84/1.52  ------ 
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  ------ Proving...
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  % SZS status Theorem for theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  fof(f10,axiom,(
% 7.84/1.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f18,plain,(
% 7.84/1.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.84/1.52    inference(ennf_transformation,[],[f10])).
% 7.84/1.52  
% 7.84/1.52  fof(f37,plain,(
% 7.84/1.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f18])).
% 7.84/1.52  
% 7.84/1.52  fof(f1,axiom,(
% 7.84/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f26,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f1])).
% 7.84/1.52  
% 7.84/1.52  fof(f7,axiom,(
% 7.84/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f34,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.84/1.52    inference(cnf_transformation,[],[f7])).
% 7.84/1.52  
% 7.84/1.52  fof(f42,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.84/1.52    inference(definition_unfolding,[],[f26,f34,f34])).
% 7.84/1.52  
% 7.84/1.52  fof(f4,axiom,(
% 7.84/1.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f14,plain,(
% 7.84/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.84/1.52    inference(ennf_transformation,[],[f4])).
% 7.84/1.52  
% 7.84/1.52  fof(f15,plain,(
% 7.84/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.84/1.52    inference(flattening,[],[f14])).
% 7.84/1.52  
% 7.84/1.52  fof(f31,plain,(
% 7.84/1.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f15])).
% 7.84/1.52  
% 7.84/1.52  fof(f12,conjecture,(
% 7.84/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f13,negated_conjecture,(
% 7.84/1.52    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.84/1.52    inference(negated_conjecture,[],[f12])).
% 7.84/1.52  
% 7.84/1.52  fof(f20,plain,(
% 7.84/1.52    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.84/1.52    inference(ennf_transformation,[],[f13])).
% 7.84/1.52  
% 7.84/1.52  fof(f21,plain,(
% 7.84/1.52    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 7.84/1.52    inference(flattening,[],[f20])).
% 7.84/1.52  
% 7.84/1.52  fof(f24,plain,(
% 7.84/1.52    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 7.84/1.52    introduced(choice_axiom,[])).
% 7.84/1.52  
% 7.84/1.52  fof(f25,plain,(
% 7.84/1.52    k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 7.84/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 7.84/1.52  
% 7.84/1.52  fof(f40,plain,(
% 7.84/1.52    r1_tarski(sK0,k1_relat_1(sK1))),
% 7.84/1.52    inference(cnf_transformation,[],[f25])).
% 7.84/1.52  
% 7.84/1.52  fof(f8,axiom,(
% 7.84/1.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f16,plain,(
% 7.84/1.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 7.84/1.52    inference(ennf_transformation,[],[f8])).
% 7.84/1.52  
% 7.84/1.52  fof(f17,plain,(
% 7.84/1.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 7.84/1.52    inference(flattening,[],[f16])).
% 7.84/1.52  
% 7.84/1.52  fof(f35,plain,(
% 7.84/1.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f17])).
% 7.84/1.52  
% 7.84/1.52  fof(f9,axiom,(
% 7.84/1.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f36,plain,(
% 7.84/1.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f9])).
% 7.84/1.52  
% 7.84/1.52  fof(f5,axiom,(
% 7.84/1.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f32,plain,(
% 7.84/1.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f5])).
% 7.84/1.52  
% 7.84/1.52  fof(f11,axiom,(
% 7.84/1.52    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f19,plain,(
% 7.84/1.52    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.84/1.52    inference(ennf_transformation,[],[f11])).
% 7.84/1.52  
% 7.84/1.52  fof(f38,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f19])).
% 7.84/1.52  
% 7.84/1.52  fof(f43,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.84/1.52    inference(definition_unfolding,[],[f38,f34])).
% 7.84/1.52  
% 7.84/1.52  fof(f39,plain,(
% 7.84/1.52    v1_relat_1(sK1)),
% 7.84/1.52    inference(cnf_transformation,[],[f25])).
% 7.84/1.52  
% 7.84/1.52  fof(f2,axiom,(
% 7.84/1.52    v1_xboole_0(k1_xboole_0)),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f27,plain,(
% 7.84/1.52    v1_xboole_0(k1_xboole_0)),
% 7.84/1.52    inference(cnf_transformation,[],[f2])).
% 7.84/1.52  
% 7.84/1.52  fof(f3,axiom,(
% 7.84/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f22,plain,(
% 7.84/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.52    inference(nnf_transformation,[],[f3])).
% 7.84/1.52  
% 7.84/1.52  fof(f23,plain,(
% 7.84/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.52    inference(flattening,[],[f22])).
% 7.84/1.52  
% 7.84/1.52  fof(f30,plain,(
% 7.84/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f23])).
% 7.84/1.52  
% 7.84/1.52  fof(f28,plain,(
% 7.84/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.84/1.52    inference(cnf_transformation,[],[f23])).
% 7.84/1.52  
% 7.84/1.52  fof(f45,plain,(
% 7.84/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.84/1.52    inference(equality_resolution,[],[f28])).
% 7.84/1.52  
% 7.84/1.52  fof(f6,axiom,(
% 7.84/1.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f33,plain,(
% 7.84/1.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.84/1.52    inference(cnf_transformation,[],[f6])).
% 7.84/1.52  
% 7.84/1.52  fof(f41,plain,(
% 7.84/1.52    k1_relat_1(k7_relat_1(sK1,sK0)) != sK0),
% 7.84/1.52    inference(cnf_transformation,[],[f25])).
% 7.84/1.52  
% 7.84/1.52  cnf(c_10,plain,
% 7.84/1.52      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 7.84/1.52      inference(cnf_transformation,[],[f37]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_450,plain,
% 7.84/1.52      ( ~ v1_xboole_0(X0)
% 7.84/1.52      | ~ v1_xboole_0(k4_xboole_0(X1,X2))
% 7.84/1.52      | X0 = k4_xboole_0(X1,X2) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_542,plain,
% 7.84/1.52      ( ~ v1_xboole_0(k4_xboole_0(X0,X1))
% 7.84/1.52      | ~ v1_xboole_0(k1_xboole_0)
% 7.84/1.52      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_450]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_31260,plain,
% 7.84/1.52      ( ~ v1_xboole_0(k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | ~ v1_xboole_0(k1_xboole_0)
% 7.84/1.52      | k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_542]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_216,plain,
% 7.84/1.52      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 7.84/1.52      theory(equality) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_10200,plain,
% 7.84/1.52      ( X0 != k4_xboole_0(sK0,k1_relat_1(sK1))
% 7.84/1.52      | X1 != sK0
% 7.84/1.52      | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_216]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_31257,plain,
% 7.84/1.52      ( X0 != sK0
% 7.84/1.52      | k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | k1_xboole_0 != k4_xboole_0(sK0,k1_relat_1(sK1)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_10200]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_31261,plain,
% 7.84/1.52      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | sK0 != sK0
% 7.84/1.52      | k1_xboole_0 != k4_xboole_0(sK0,k1_relat_1(sK1)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_31257]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_215,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_517,plain,
% 7.84/1.52      ( X0 != X1
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != X1
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = X0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_215]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_3744,plain,
% 7.84/1.52      ( X0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = X0
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_517]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_10199,plain,
% 7.84/1.52      ( k4_xboole_0(X0,X1) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(X0,X1)
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_3744]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_30842,plain,
% 7.84/1.52      ( k4_xboole_0(X0,k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(X0,k1_xboole_0)
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_10199]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_30844,plain,
% 7.84/1.52      ( k4_xboole_0(sK0,k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_30842]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_469,plain,
% 7.84/1.52      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X0
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 7.84/1.52      | sK0 != X0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_215]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_3049,plain,
% 7.84/1.52      ( k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(X0,k1_xboole_0)
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 7.84/1.52      | sK0 != k4_xboole_0(X0,k1_xboole_0) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_469]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_3050,plain,
% 7.84/1.52      ( k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(sK0,k1_xboole_0)
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 7.84/1.52      | sK0 != k4_xboole_0(sK0,k1_xboole_0) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_3049]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_0,plain,
% 7.84/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.84/1.52      inference(cnf_transformation,[],[f42]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1575,plain,
% 7.84/1.52      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_865,plain,
% 7.84/1.52      ( X0 != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = X0
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_517]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1574,plain,
% 7.84/1.52      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_865]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_801,plain,
% 7.84/1.52      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_215]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1426,plain,
% 7.84/1.52      ( X0 != X1
% 7.84/1.52      | X0 = k4_xboole_0(X1,k1_xboole_0)
% 7.84/1.52      | k4_xboole_0(X1,k1_xboole_0) != X1 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_801]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1427,plain,
% 7.84/1.52      ( k4_xboole_0(sK0,k1_xboole_0) != sK0
% 7.84/1.52      | sK0 = k4_xboole_0(sK0,k1_xboole_0)
% 7.84/1.52      | sK0 != sK0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_1426]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_689,plain,
% 7.84/1.52      ( X0 != k1_relat_1(k7_relat_1(sK1,sK0))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = X0
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_517]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_851,plain,
% 7.84/1.52      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != k1_relat_1(k7_relat_1(sK1,sK0))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))
% 7.84/1.52      | k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_689]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_5,plain,
% 7.84/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.84/1.52      inference(cnf_transformation,[],[f31]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_13,negated_conjecture,
% 7.84/1.52      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 7.84/1.52      inference(cnf_transformation,[],[f40]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_635,plain,
% 7.84/1.52      ( r1_tarski(X0,k1_relat_1(sK1)) | ~ r1_tarski(X0,sK0) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_5,c_13]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_8,plain,
% 7.84/1.52      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 7.84/1.52      inference(cnf_transformation,[],[f35]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_9,plain,
% 7.84/1.52      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.84/1.52      inference(cnf_transformation,[],[f36]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_141,plain,
% 7.84/1.52      ( ~ r1_tarski(X0,X1)
% 7.84/1.52      | v1_xboole_0(X0)
% 7.84/1.52      | X2 != X1
% 7.84/1.52      | k4_xboole_0(X3,X2) != X0 ),
% 7.84/1.52      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_142,plain,
% 7.84/1.52      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
% 7.84/1.52      | v1_xboole_0(k4_xboole_0(X0,X1)) ),
% 7.84/1.52      inference(unflattening,[status(thm)],[c_141]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_645,plain,
% 7.84/1.52      ( ~ r1_tarski(k4_xboole_0(X0,k1_relat_1(sK1)),sK0)
% 7.84/1.52      | v1_xboole_0(k4_xboole_0(X0,k1_relat_1(sK1))) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_635,c_142]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_6,plain,
% 7.84/1.52      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.84/1.52      inference(cnf_transformation,[],[f32]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_779,plain,
% 7.84/1.52      ( v1_xboole_0(k4_xboole_0(sK0,k1_relat_1(sK1))) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_645,c_6]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_214,plain,( X0 = X0 ),theory(equality) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_516,plain,
% 7.84/1.52      ( k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_214]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_11,plain,
% 7.84/1.52      ( ~ v1_relat_1(X0)
% 7.84/1.52      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 7.84/1.52      inference(cnf_transformation,[],[f43]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_14,negated_conjecture,
% 7.84/1.52      ( v1_relat_1(sK1) ),
% 7.84/1.52      inference(cnf_transformation,[],[f39]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_134,plain,
% 7.84/1.52      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 7.84/1.52      | sK1 != X0 ),
% 7.84/1.52      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_135,plain,
% 7.84/1.52      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 7.84/1.52      inference(unflattening,[status(thm)],[c_134]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_136,plain,
% 7.84/1.52      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_135]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1,plain,
% 7.84/1.52      ( v1_xboole_0(k1_xboole_0) ),
% 7.84/1.52      inference(cnf_transformation,[],[f27]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2,plain,
% 7.84/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.84/1.52      inference(cnf_transformation,[],[f30]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_39,plain,
% 7.84/1.52      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_4,plain,
% 7.84/1.52      ( r1_tarski(X0,X0) ),
% 7.84/1.52      inference(cnf_transformation,[],[f45]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_35,plain,
% 7.84/1.52      ( r1_tarski(sK0,sK0) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_4]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_7,plain,
% 7.84/1.52      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.84/1.52      inference(cnf_transformation,[],[f33]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_29,plain,
% 7.84/1.52      ( k4_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_12,negated_conjecture,
% 7.84/1.52      ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
% 7.84/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(contradiction,plain,
% 7.84/1.52      ( $false ),
% 7.84/1.52      inference(minisat,
% 7.84/1.52                [status(thm)],
% 7.84/1.52                [c_31260,c_31261,c_30844,c_3050,c_1575,c_1574,c_1427,
% 7.84/1.52                 c_851,c_779,c_516,c_136,c_1,c_39,c_35,c_29,c_12]) ).
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  ------                               Statistics
% 7.84/1.52  
% 7.84/1.52  ------ Selected
% 7.84/1.52  
% 7.84/1.52  total_time:                             0.898
% 7.84/1.52  
%------------------------------------------------------------------------------
