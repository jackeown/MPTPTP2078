%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0607+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:43 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   31 (  51 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   14
%              Number of atoms          :   69 ( 134 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k1_relat_1(X2),X0)
         => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) != k7_relat_1(X2,k6_subset_1(X0,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) != k7_relat_1(X2,k6_subset_1(X0,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k6_subset_1(X2,k7_relat_1(X2,X1)) != k7_relat_1(X2,k6_subset_1(X0,X1))
        & r1_tarski(k1_relat_1(X2),X0)
        & v1_relat_1(X2) )
   => ( k6_subset_1(sK2,k7_relat_1(sK2,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1))
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( k6_subset_1(sK2,k7_relat_1(sK2,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1))
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f15,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,plain,(
    k6_subset_1(sK2,k7_relat_1(sK2,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_50,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_51,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,sK0) = X0
    | k1_relat_1(X0) != k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_50])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_69,plain,
    ( k7_relat_1(X0,sK0) = X0
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_4])).

cnf(c_70,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_69])).

cnf(c_86,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_70])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_77,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_78,plain,
    ( k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) = k7_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_77])).

cnf(c_99,plain,
    ( k6_subset_1(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k6_subset_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_86,c_78])).

cnf(c_2,negated_conjecture,
    ( k6_subset_1(sK2,k7_relat_1(sK2,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_102,plain,
    ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k7_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_99,c_2])).

cnf(c_105,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_102])).


%------------------------------------------------------------------------------
