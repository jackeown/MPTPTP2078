%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0666+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:51 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   36 (  68 expanded)
%              Number of clauses        :   18 (  20 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 236 expanded)
%              Number of equality atoms :   49 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
          | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
        | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f18,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_2,negated_conjecture,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_92,negated_conjecture,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_45,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | sK1 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_46,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,sK1),sK0) = k7_relat_1(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_45])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_80,plain,
    ( k7_relat_1(k7_relat_1(X0,sK1),sK0) = k7_relat_1(X0,sK0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_4])).

cnf(c_81,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0) ),
    inference(unflattening,[status(thm)],[c_80])).

cnf(c_90,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_81])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_57,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_58,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,sK0),sK1) = k7_relat_1(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_57])).

cnf(c_75,plain,
    ( k7_relat_1(k7_relat_1(X0,sK0),sK1) = k7_relat_1(X0,sK0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_58,c_4])).

cnf(c_76,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0) ),
    inference(unflattening,[status(thm)],[c_75])).

cnf(c_91,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_76])).

cnf(c_102,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,sK0) ),
    inference(light_normalisation,[status(thm)],[c_92,c_90,c_91])).

cnf(c_103,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_102])).


%------------------------------------------------------------------------------
