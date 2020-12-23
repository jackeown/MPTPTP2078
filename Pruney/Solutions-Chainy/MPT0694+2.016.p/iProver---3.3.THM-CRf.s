%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:58 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 109 expanded)
%              Number of clauses        :   34 (  37 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 ( 292 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f43,f43])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f55,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f55,f43,f43])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1574,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X2)
    | X2 != X1
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != X0 ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_4480,plain,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),X0)
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1)
    | X1 != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_8894,plain,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),k10_relat_1(sK2,sK1))
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0)
    | X0 != k10_relat_1(sK2,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_4480])).

cnf(c_21348,plain,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),k10_relat_1(sK2,sK1))
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | k10_relat_1(sK2,sK1) != k10_relat_1(sK2,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_8894])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3026,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),X0),k10_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8893,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),k10_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_282,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3684,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_927,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(X0,X1))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1)
    | ~ r1_tarski(sK2,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2808,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(X0,sK0))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ r1_tarski(sK2,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_2810,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2808])).

cnf(c_1569,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_975,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) = k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_814,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_171,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_172,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_176,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_172,c_16])).

cnf(c_788,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_669,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_787,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_602,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_47,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21348,c_8893,c_3684,c_2810,c_1569,c_975,c_814,c_788,c_787,c_602,c_47,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:37:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.66/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.49  
% 7.66/1.49  ------  iProver source info
% 7.66/1.49  
% 7.66/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.49  git: non_committed_changes: false
% 7.66/1.49  git: last_make_outside_of_git: false
% 7.66/1.49  
% 7.66/1.49  ------ 
% 7.66/1.49  ------ Parsing...
% 7.66/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.49  ------ Proving...
% 7.66/1.49  ------ Problem Properties 
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  clauses                                 15
% 7.66/1.49  conjectures                             2
% 7.66/1.49  EPR                                     4
% 7.66/1.49  Horn                                    15
% 7.66/1.49  unary                                   7
% 7.66/1.49  binary                                  4
% 7.66/1.49  lits                                    29
% 7.66/1.49  lits eq                                 5
% 7.66/1.49  fd_pure                                 0
% 7.66/1.49  fd_pseudo                               0
% 7.66/1.49  fd_cond                                 0
% 7.66/1.49  fd_pseudo_cond                          1
% 7.66/1.49  AC symbols                              0
% 7.66/1.49  
% 7.66/1.49  ------ Input Options Time Limit: Unbounded
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  ------ 
% 7.66/1.49  Current options:
% 7.66/1.49  ------ 
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  ------ Proving...
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  % SZS status Theorem for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  fof(f5,axiom,(
% 7.66/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f42,plain,(
% 7.66/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f5])).
% 7.66/1.49  
% 7.66/1.49  fof(f13,axiom,(
% 7.66/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f25,plain,(
% 7.66/1.49    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 7.66/1.49    inference(ennf_transformation,[],[f13])).
% 7.66/1.49  
% 7.66/1.49  fof(f26,plain,(
% 7.66/1.49    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 7.66/1.49    inference(flattening,[],[f25])).
% 7.66/1.49  
% 7.66/1.49  fof(f50,plain,(
% 7.66/1.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f26])).
% 7.66/1.49  
% 7.66/1.49  fof(f1,axiom,(
% 7.66/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f36,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f1])).
% 7.66/1.49  
% 7.66/1.49  fof(f6,axiom,(
% 7.66/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f43,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.66/1.49    inference(cnf_transformation,[],[f6])).
% 7.66/1.49  
% 7.66/1.49  fof(f57,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.66/1.49    inference(definition_unfolding,[],[f36,f43,f43])).
% 7.66/1.49  
% 7.66/1.49  fof(f15,axiom,(
% 7.66/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f28,plain,(
% 7.66/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.66/1.49    inference(ennf_transformation,[],[f15])).
% 7.66/1.49  
% 7.66/1.49  fof(f29,plain,(
% 7.66/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.66/1.49    inference(flattening,[],[f28])).
% 7.66/1.49  
% 7.66/1.49  fof(f52,plain,(
% 7.66/1.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f29])).
% 7.66/1.49  
% 7.66/1.49  fof(f16,conjecture,(
% 7.66/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f17,negated_conjecture,(
% 7.66/1.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 7.66/1.49    inference(negated_conjecture,[],[f16])).
% 7.66/1.49  
% 7.66/1.49  fof(f30,plain,(
% 7.66/1.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.66/1.49    inference(ennf_transformation,[],[f17])).
% 7.66/1.49  
% 7.66/1.49  fof(f31,plain,(
% 7.66/1.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.66/1.49    inference(flattening,[],[f30])).
% 7.66/1.49  
% 7.66/1.49  fof(f34,plain,(
% 7.66/1.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f35,plain,(
% 7.66/1.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.66/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34])).
% 7.66/1.49  
% 7.66/1.49  fof(f54,plain,(
% 7.66/1.49    v1_funct_1(sK2)),
% 7.66/1.49    inference(cnf_transformation,[],[f35])).
% 7.66/1.49  
% 7.66/1.49  fof(f53,plain,(
% 7.66/1.49    v1_relat_1(sK2)),
% 7.66/1.49    inference(cnf_transformation,[],[f35])).
% 7.66/1.49  
% 7.66/1.49  fof(f4,axiom,(
% 7.66/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f20,plain,(
% 7.66/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.66/1.49    inference(ennf_transformation,[],[f4])).
% 7.66/1.49  
% 7.66/1.49  fof(f21,plain,(
% 7.66/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.66/1.49    inference(flattening,[],[f20])).
% 7.66/1.49  
% 7.66/1.49  fof(f41,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f21])).
% 7.66/1.49  
% 7.66/1.49  fof(f3,axiom,(
% 7.66/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f18,plain,(
% 7.66/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.66/1.49    inference(ennf_transformation,[],[f3])).
% 7.66/1.49  
% 7.66/1.49  fof(f19,plain,(
% 7.66/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.66/1.49    inference(flattening,[],[f18])).
% 7.66/1.49  
% 7.66/1.49  fof(f40,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f19])).
% 7.66/1.49  
% 7.66/1.49  fof(f58,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.66/1.49    inference(definition_unfolding,[],[f40,f43])).
% 7.66/1.49  
% 7.66/1.49  fof(f2,axiom,(
% 7.66/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f32,plain,(
% 7.66/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.49    inference(nnf_transformation,[],[f2])).
% 7.66/1.49  
% 7.66/1.49  fof(f33,plain,(
% 7.66/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.49    inference(flattening,[],[f32])).
% 7.66/1.49  
% 7.66/1.49  fof(f37,plain,(
% 7.66/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.66/1.49    inference(cnf_transformation,[],[f33])).
% 7.66/1.49  
% 7.66/1.49  fof(f63,plain,(
% 7.66/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.66/1.49    inference(equality_resolution,[],[f37])).
% 7.66/1.49  
% 7.66/1.49  fof(f55,plain,(
% 7.66/1.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 7.66/1.49    inference(cnf_transformation,[],[f35])).
% 7.66/1.49  
% 7.66/1.49  fof(f61,plain,(
% 7.66/1.49    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 7.66/1.49    inference(definition_unfolding,[],[f55,f43,f43])).
% 7.66/1.49  
% 7.66/1.49  cnf(c_285,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.66/1.49      theory(equality) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1574,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,X1)
% 7.66/1.49      | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X2)
% 7.66/1.49      | X2 != X1
% 7.66/1.49      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != X0 ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_285]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_4480,plain,
% 7.66/1.49      ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),X0)
% 7.66/1.49      | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1)
% 7.66/1.49      | X1 != X0
% 7.66/1.49      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1574]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_8894,plain,
% 7.66/1.49      ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),k10_relat_1(sK2,sK1))
% 7.66/1.49      | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0)
% 7.66/1.49      | X0 != k10_relat_1(sK2,sK1)
% 7.66/1.49      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_4480]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_21348,plain,
% 7.66/1.49      ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),k10_relat_1(sK2,sK1))
% 7.66/1.49      | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
% 7.66/1.49      | k10_relat_1(sK2,sK1) != k10_relat_1(sK2,sK1)
% 7.66/1.49      | k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_8894]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_6,plain,
% 7.66/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.66/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_3026,plain,
% 7.66/1.49      ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),X0),k10_relat_1(sK2,sK1)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_8893,plain,
% 7.66/1.49      ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)),k10_relat_1(sK2,sK1)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_3026]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_282,plain,( X0 = X0 ),theory(equality) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_3684,plain,
% 7.66/1.49      ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_282]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_11,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,X1)
% 7.66/1.49      | ~ r1_tarski(X2,X3)
% 7.66/1.49      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
% 7.66/1.49      | ~ v1_relat_1(X2)
% 7.66/1.49      | ~ v1_relat_1(X3) ),
% 7.66/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_927,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(X0,X1))
% 7.66/1.49      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1)
% 7.66/1.49      | ~ r1_tarski(sK2,X0)
% 7.66/1.49      | ~ v1_relat_1(X0)
% 7.66/1.49      | ~ v1_relat_1(sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2808,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(X0,sK0))
% 7.66/1.49      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
% 7.66/1.49      | ~ r1_tarski(sK2,X0)
% 7.66/1.49      | ~ v1_relat_1(X0)
% 7.66/1.49      | ~ v1_relat_1(sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_927]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2810,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 7.66/1.49      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
% 7.66/1.49      | ~ r1_tarski(sK2,sK2)
% 7.66/1.49      | ~ v1_relat_1(sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_2808]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1569,plain,
% 7.66/1.49      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_0,plain,
% 7.66/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_975,plain,
% 7.66/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) = k4_xboole_0(k10_relat_1(sK2,sK1),k4_xboole_0(k10_relat_1(sK2,sK1),sK0)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_814,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
% 7.66/1.49      | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
% 7.66/1.49      | ~ r1_tarski(sK2,sK2)
% 7.66/1.49      | ~ v1_relat_1(sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_13,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.66/1.49      | ~ v1_funct_1(X0)
% 7.66/1.49      | ~ v1_relat_1(X0) ),
% 7.66/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_15,negated_conjecture,
% 7.66/1.49      ( v1_funct_1(sK2) ),
% 7.66/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_171,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.66/1.49      | ~ v1_relat_1(X0)
% 7.66/1.49      | sK2 != X0 ),
% 7.66/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_172,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 7.66/1.49      | ~ v1_relat_1(sK2) ),
% 7.66/1.49      inference(unflattening,[status(thm)],[c_171]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_16,negated_conjecture,
% 7.66/1.49      ( v1_relat_1(sK2) ),
% 7.66/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_176,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_172,c_16]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_788,plain,
% 7.66/1.49      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_176]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.66/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_669,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,sK1)
% 7.66/1.49      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0)
% 7.66/1.49      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_787,plain,
% 7.66/1.49      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
% 7.66/1.49      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
% 7.66/1.49      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_669]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_4,plain,
% 7.66/1.49      ( ~ r1_tarski(X0,X1)
% 7.66/1.49      | ~ r1_tarski(X0,X2)
% 7.66/1.49      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.66/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_602,plain,
% 7.66/1.49      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 7.66/1.49      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))
% 7.66/1.49      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_3,plain,
% 7.66/1.49      ( r1_tarski(X0,X0) ),
% 7.66/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_47,plain,
% 7.66/1.49      ( r1_tarski(sK2,sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_14,negated_conjecture,
% 7.66/1.49      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
% 7.66/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(contradiction,plain,
% 7.66/1.49      ( $false ),
% 7.66/1.49      inference(minisat,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_21348,c_8893,c_3684,c_2810,c_1569,c_975,c_814,c_788,
% 7.66/1.49                 c_787,c_602,c_47,c_14,c_16]) ).
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  ------                               Statistics
% 7.66/1.49  
% 7.66/1.49  ------ Selected
% 7.66/1.49  
% 7.66/1.49  total_time:                             0.688
% 7.66/1.49  
%------------------------------------------------------------------------------
