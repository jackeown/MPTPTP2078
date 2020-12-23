%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:04 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 142 expanded)
%              Number of clauses        :   49 (  58 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  209 ( 355 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f33])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f25,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(sK2)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f46,f58,f57])).

fof(f97,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1062,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1061,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6157,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1062,c_1061])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_10655,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6157,c_16])).

cnf(c_1064,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_10947,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10655,c_1064])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1854,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1848,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5400,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_1848])).

cnf(c_6106,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5400,c_1848])).

cnf(c_6406,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6106,c_1848])).

cnf(c_13,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1843,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1842,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2428,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1843,c_1842])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1840,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5383,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_1840])).

cnf(c_16789,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6406,c_5383])).

cnf(c_16808,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16789])).

cnf(c_27751,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10947,c_16808])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_12,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4090,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_5643,plain,
    ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_17,c_4090])).

cnf(c_27781,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(resolution,[status(thm)],[c_27751,c_5643])).

cnf(c_27875,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_27781,c_1])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_5586,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_10,c_35])).

cnf(c_7299,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_33,c_5586])).

cnf(c_36,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_7486,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7299,c_36])).

cnf(c_7487,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_7486])).

cnf(c_7506,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_7487,c_33])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_7643,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7506,c_37])).

cnf(c_7644,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_7643])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7650,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7644,c_9])).

cnf(c_28469,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_27875,c_7650])).

cnf(c_29,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2083,plain,
    ( v1_relat_1(k3_xboole_0(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_20996,plain,
    ( v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28469,c_20996,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.69/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.69/1.49  
% 6.69/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.69/1.49  
% 6.69/1.49  ------  iProver source info
% 6.69/1.49  
% 6.69/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.69/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.69/1.49  git: non_committed_changes: false
% 6.69/1.49  git: last_make_outside_of_git: false
% 6.69/1.49  
% 6.69/1.49  ------ 
% 6.69/1.49  ------ Parsing...
% 6.69/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.69/1.49  
% 6.69/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.69/1.49  
% 6.69/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.69/1.49  
% 6.69/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.69/1.49  ------ Proving...
% 6.69/1.49  ------ Problem Properties 
% 6.69/1.49  
% 6.69/1.49  
% 6.69/1.49  clauses                                 33
% 6.69/1.49  conjectures                             3
% 6.69/1.49  EPR                                     6
% 6.69/1.49  Horn                                    32
% 6.69/1.49  unary                                   8
% 6.69/1.49  binary                                  15
% 6.69/1.49  lits                                    70
% 6.69/1.49  lits eq                                 9
% 6.69/1.49  fd_pure                                 0
% 6.69/1.49  fd_pseudo                               0
% 6.69/1.49  fd_cond                                 1
% 6.69/1.49  fd_pseudo_cond                          4
% 6.69/1.49  AC symbols                              0
% 6.69/1.49  
% 6.69/1.49  ------ Input Options Time Limit: Unbounded
% 6.69/1.49  
% 6.69/1.49  
% 6.69/1.49  ------ 
% 6.69/1.49  Current options:
% 6.69/1.49  ------ 
% 6.69/1.49  
% 6.69/1.49  
% 6.69/1.49  
% 6.69/1.49  
% 6.69/1.49  ------ Proving...
% 6.69/1.49  
% 6.69/1.49  
% 6.69/1.49  % SZS status Theorem for theBenchmark.p
% 6.69/1.49  
% 6.69/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.69/1.49  
% 6.69/1.49  fof(f12,axiom,(
% 6.69/1.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f32,plain,(
% 6.69/1.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 6.69/1.49    inference(ennf_transformation,[],[f12])).
% 6.69/1.49  
% 6.69/1.49  fof(f76,plain,(
% 6.69/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f32])).
% 6.69/1.49  
% 6.69/1.49  fof(f1,axiom,(
% 6.69/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f47,plain,(
% 6.69/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.69/1.49    inference(nnf_transformation,[],[f1])).
% 6.69/1.49  
% 6.69/1.49  fof(f48,plain,(
% 6.69/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.69/1.49    inference(flattening,[],[f47])).
% 6.69/1.49  
% 6.69/1.49  fof(f61,plain,(
% 6.69/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.69/1.49    inference(cnf_transformation,[],[f48])).
% 6.69/1.49  
% 6.69/1.49  fof(f98,plain,(
% 6.69/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.69/1.49    inference(equality_resolution,[],[f61])).
% 6.69/1.49  
% 6.69/1.49  fof(f5,axiom,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f29,plain,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 6.69/1.49    inference(ennf_transformation,[],[f5])).
% 6.69/1.49  
% 6.69/1.49  fof(f68,plain,(
% 6.69/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f29])).
% 6.69/1.49  
% 6.69/1.49  fof(f10,axiom,(
% 6.69/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f73,plain,(
% 6.69/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f10])).
% 6.69/1.49  
% 6.69/1.49  fof(f14,axiom,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f35,plain,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 6.69/1.49    inference(ennf_transformation,[],[f14])).
% 6.69/1.49  
% 6.69/1.49  fof(f78,plain,(
% 6.69/1.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f35])).
% 6.69/1.49  
% 6.69/1.49  fof(f13,axiom,(
% 6.69/1.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f33,plain,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 6.69/1.49    inference(ennf_transformation,[],[f13])).
% 6.69/1.49  
% 6.69/1.49  fof(f34,plain,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.69/1.49    inference(flattening,[],[f33])).
% 6.69/1.49  
% 6.69/1.49  fof(f77,plain,(
% 6.69/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.69/1.49    inference(cnf_transformation,[],[f34])).
% 6.69/1.49  
% 6.69/1.49  fof(f9,axiom,(
% 6.69/1.49    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f72,plain,(
% 6.69/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 6.69/1.49    inference(cnf_transformation,[],[f9])).
% 6.69/1.49  
% 6.69/1.49  fof(f24,axiom,(
% 6.69/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f44,plain,(
% 6.69/1.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.69/1.49    inference(ennf_transformation,[],[f24])).
% 6.69/1.49  
% 6.69/1.49  fof(f45,plain,(
% 6.69/1.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.69/1.49    inference(flattening,[],[f44])).
% 6.69/1.49  
% 6.69/1.49  fof(f94,plain,(
% 6.69/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f45])).
% 6.69/1.49  
% 6.69/1.49  fof(f7,axiom,(
% 6.69/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f30,plain,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 6.69/1.49    inference(ennf_transformation,[],[f7])).
% 6.69/1.49  
% 6.69/1.49  fof(f31,plain,(
% 6.69/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 6.69/1.49    inference(flattening,[],[f30])).
% 6.69/1.49  
% 6.69/1.49  fof(f70,plain,(
% 6.69/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f31])).
% 6.69/1.49  
% 6.69/1.49  fof(f25,conjecture,(
% 6.69/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f26,negated_conjecture,(
% 6.69/1.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 6.69/1.49    inference(negated_conjecture,[],[f25])).
% 6.69/1.49  
% 6.69/1.49  fof(f46,plain,(
% 6.69/1.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 6.69/1.49    inference(ennf_transformation,[],[f26])).
% 6.69/1.49  
% 6.69/1.49  fof(f58,plain,(
% 6.69/1.49    ( ! [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(sK2))) & v1_relat_1(sK2))) )),
% 6.69/1.49    introduced(choice_axiom,[])).
% 6.69/1.49  
% 6.69/1.49  fof(f57,plain,(
% 6.69/1.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 6.69/1.49    introduced(choice_axiom,[])).
% 6.69/1.49  
% 6.69/1.49  fof(f59,plain,(
% 6.69/1.49    (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 6.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f46,f58,f57])).
% 6.69/1.49  
% 6.69/1.49  fof(f97,plain,(
% 6.69/1.49    ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))),
% 6.69/1.49    inference(cnf_transformation,[],[f59])).
% 6.69/1.49  
% 6.69/1.49  fof(f96,plain,(
% 6.69/1.49    v1_relat_1(sK2)),
% 6.69/1.49    inference(cnf_transformation,[],[f59])).
% 6.69/1.49  
% 6.69/1.49  fof(f95,plain,(
% 6.69/1.49    v1_relat_1(sK1)),
% 6.69/1.49    inference(cnf_transformation,[],[f59])).
% 6.69/1.49  
% 6.69/1.49  fof(f6,axiom,(
% 6.69/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f69,plain,(
% 6.69/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f6])).
% 6.69/1.49  
% 6.69/1.49  fof(f20,axiom,(
% 6.69/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 6.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.49  
% 6.69/1.49  fof(f40,plain,(
% 6.69/1.49    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 6.69/1.49    inference(ennf_transformation,[],[f20])).
% 6.69/1.49  
% 6.69/1.49  fof(f89,plain,(
% 6.69/1.49    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 6.69/1.49    inference(cnf_transformation,[],[f40])).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1062,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1061,plain,( X0 = X0 ),theory(equality) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_6157,plain,
% 6.69/1.49      ( X0 != X1 | X1 = X0 ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_1062,c_1061]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_16,plain,
% 6.69/1.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 6.69/1.49      inference(cnf_transformation,[],[f76]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_10655,plain,
% 6.69/1.49      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k1_xboole_0 ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_6157,c_16]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1064,plain,
% 6.69/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,X2) | X2 != X1 ),
% 6.69/1.49      theory(equality) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_10947,plain,
% 6.69/1.49      ( r1_xboole_0(X0,X1)
% 6.69/1.49      | ~ r1_xboole_0(X0,k1_xboole_0)
% 6.69/1.49      | ~ r1_tarski(X1,k1_xboole_0) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_10655,c_1064]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1,plain,
% 6.69/1.49      ( r1_tarski(X0,X0) ),
% 6.69/1.49      inference(cnf_transformation,[],[f98]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1854,plain,
% 6.69/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 6.69/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_8,plain,
% 6.69/1.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 6.69/1.49      inference(cnf_transformation,[],[f68]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1848,plain,
% 6.69/1.49      ( r1_tarski(X0,X1) = iProver_top
% 6.69/1.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 6.69/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_5400,plain,
% 6.69/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 6.69/1.49      inference(superposition,[status(thm)],[c_1854,c_1848]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_6106,plain,
% 6.69/1.49      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 6.69/1.49      inference(superposition,[status(thm)],[c_5400,c_1848]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_6406,plain,
% 6.69/1.49      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = iProver_top ),
% 6.69/1.49      inference(superposition,[status(thm)],[c_6106,c_1848]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_13,plain,
% 6.69/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 6.69/1.49      inference(cnf_transformation,[],[f73]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1843,plain,
% 6.69/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 6.69/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1842,plain,
% 6.69/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.69/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_2428,plain,
% 6.69/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.69/1.49      inference(superposition,[status(thm)],[c_1843,c_1842]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_18,plain,
% 6.69/1.49      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 6.69/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_1840,plain,
% 6.69/1.49      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 6.69/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 6.69/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_5383,plain,
% 6.69/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 6.69/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 6.69/1.49      inference(superposition,[status(thm)],[c_2428,c_1840]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_16789,plain,
% 6.69/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 6.69/1.49      inference(superposition,[status(thm)],[c_6406,c_5383]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_16808,plain,
% 6.69/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 6.69/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_16789]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_27751,plain,
% 6.69/1.49      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 6.69/1.49      inference(global_propositional_subsumption,
% 6.69/1.49                [status(thm)],
% 6.69/1.49                [c_10947,c_16808]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_17,plain,
% 6.69/1.49      ( ~ r1_xboole_0(X0,X1)
% 6.69/1.49      | r1_tarski(X0,X2)
% 6.69/1.49      | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 6.69/1.49      inference(cnf_transformation,[],[f77]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_12,plain,
% 6.69/1.49      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 6.69/1.49      inference(cnf_transformation,[],[f72]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_4090,plain,
% 6.69/1.49      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_5643,plain,
% 6.69/1.49      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 6.69/1.49      | r1_tarski(k3_xboole_0(X0,X1),X1) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_17,c_4090]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_27781,plain,
% 6.69/1.49      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(k3_xboole_0(X1,X2),X2) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_27751,c_5643]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_27875,plain,
% 6.69/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_27781,c_1]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_33,plain,
% 6.69/1.49      ( ~ r1_tarski(X0,X1)
% 6.69/1.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 6.69/1.49      | ~ v1_relat_1(X0)
% 6.69/1.49      | ~ v1_relat_1(X1) ),
% 6.69/1.49      inference(cnf_transformation,[],[f94]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_10,plain,
% 6.69/1.49      ( ~ r1_tarski(X0,X1)
% 6.69/1.49      | ~ r1_tarski(X0,X2)
% 6.69/1.49      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 6.69/1.49      inference(cnf_transformation,[],[f70]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_35,negated_conjecture,
% 6.69/1.49      ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) ),
% 6.69/1.49      inference(cnf_transformation,[],[f97]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_5586,plain,
% 6.69/1.49      ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK2))
% 6.69/1.49      | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1)) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_10,c_35]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_7299,plain,
% 6.69/1.49      ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
% 6.69/1.49      | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
% 6.69/1.49      | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
% 6.69/1.49      | ~ v1_relat_1(sK2) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_33,c_5586]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_36,negated_conjecture,
% 6.69/1.49      ( v1_relat_1(sK2) ),
% 6.69/1.49      inference(cnf_transformation,[],[f96]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_7486,plain,
% 6.69/1.49      ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
% 6.69/1.49      | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
% 6.69/1.49      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
% 6.69/1.49      inference(global_propositional_subsumption,
% 6.69/1.49                [status(thm)],
% 6.69/1.49                [c_7299,c_36]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_7487,plain,
% 6.69/1.49      ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
% 6.69/1.49      | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
% 6.69/1.49      | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
% 6.69/1.49      inference(renaming,[status(thm)],[c_7486]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_7506,plain,
% 6.69/1.49      ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
% 6.69/1.49      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
% 6.69/1.49      | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
% 6.69/1.49      | ~ v1_relat_1(sK1) ),
% 6.69/1.49      inference(resolution,[status(thm)],[c_7487,c_33]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_37,negated_conjecture,
% 6.69/1.49      ( v1_relat_1(sK1) ),
% 6.69/1.49      inference(cnf_transformation,[],[f95]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_7643,plain,
% 6.69/1.49      ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
% 6.69/1.49      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
% 6.69/1.49      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
% 6.69/1.49      inference(global_propositional_subsumption,
% 6.69/1.49                [status(thm)],
% 6.69/1.49                [c_7506,c_37]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_7644,plain,
% 6.69/1.49      ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
% 6.69/1.49      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
% 6.69/1.49      | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
% 6.69/1.49      inference(renaming,[status(thm)],[c_7643]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_9,plain,
% 6.69/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 6.69/1.49      inference(cnf_transformation,[],[f69]) ).
% 6.69/1.49  
% 6.69/1.49  cnf(c_7650,plain,
% 6.69/1.49      ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
% 6.69/1.49      | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
% 6.69/1.50      inference(forward_subsumption_resolution,
% 6.69/1.50                [status(thm)],
% 6.69/1.50                [c_7644,c_9]) ).
% 6.69/1.50  
% 6.69/1.50  cnf(c_28469,plain,
% 6.69/1.50      ( ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
% 6.69/1.50      inference(backward_subsumption_resolution,
% 6.69/1.50                [status(thm)],
% 6.69/1.50                [c_27875,c_7650]) ).
% 6.69/1.50  
% 6.69/1.50  cnf(c_29,plain,
% 6.69/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 6.69/1.50      inference(cnf_transformation,[],[f89]) ).
% 6.69/1.50  
% 6.69/1.50  cnf(c_2083,plain,
% 6.69/1.50      ( v1_relat_1(k3_xboole_0(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 6.69/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 6.69/1.50  
% 6.69/1.50  cnf(c_20996,plain,
% 6.69/1.50      ( v1_relat_1(k3_xboole_0(sK1,sK2)) | ~ v1_relat_1(sK1) ),
% 6.69/1.50      inference(instantiation,[status(thm)],[c_2083]) ).
% 6.69/1.50  
% 6.69/1.50  cnf(contradiction,plain,
% 6.69/1.50      ( $false ),
% 6.69/1.50      inference(minisat,[status(thm)],[c_28469,c_20996,c_37]) ).
% 6.69/1.50  
% 6.69/1.50  
% 6.69/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.69/1.50  
% 6.69/1.50  ------                               Statistics
% 6.69/1.50  
% 6.69/1.50  ------ Selected
% 6.69/1.50  
% 6.69/1.50  total_time:                             0.644
% 6.69/1.50  
%------------------------------------------------------------------------------
