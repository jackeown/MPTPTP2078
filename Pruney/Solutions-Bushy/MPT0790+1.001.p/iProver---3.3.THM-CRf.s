%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0790+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:07 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   32 (  52 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   14
%              Number of atoms          :   75 ( 140 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f16,plain,(
    k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_2,negated_conjecture,
    ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_96,negated_conjecture,
    ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | k3_relat_1(k2_wellord1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_3,negated_conjecture,
    ( v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_51,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k3_relat_1(k2_wellord1(X1,X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_52,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k3_relat_1(k2_wellord1(sK1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_51])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_56,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK1))
    | k3_relat_1(k2_wellord1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_52,c_4])).

cnf(c_0,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_72,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_73,plain,
    ( r1_tarski(k1_wellord1(sK1,X0),k3_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_72])).

cnf(c_83,plain,
    ( k1_wellord1(sK1,X0) != X1
    | k3_relat_1(k2_wellord1(sK1,X1)) = X1
    | k3_relat_1(sK1) != k3_relat_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_56,c_73])).

cnf(c_84,plain,
    ( k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0))) = k1_wellord1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_83])).

cnf(c_95,plain,
    ( k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X0_39))) = k1_wellord1(sK1,X0_39) ),
    inference(subtyping,[status(esa)],[c_84])).

cnf(c_107,plain,
    ( k1_wellord1(sK1,sK0) != k1_wellord1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_96,c_95])).

cnf(c_108,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_107])).


%------------------------------------------------------------------------------
