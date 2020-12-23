%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0944+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:28 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 129 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( r1_tarski(X1,X0)
           => v2_wellord1(k1_wellord2(X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,X0) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,X0) )
     => ( ~ v2_wellord1(k1_wellord2(sK1))
        & r1_tarski(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(k1_wellord2(X1))
            & r1_tarski(X1,X0) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ v2_wellord1(k1_wellord2(sK1))
    & r1_tarski(sK1,sK0)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).

fof(f20,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ~ v2_wellord1(k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_91,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_92,plain,
    ( k2_wellord1(k1_wellord2(sK0),sK1) = k1_wellord2(sK1) ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_138,plain,
    ( k2_wellord1(k1_wellord2(sK0),sK1) = k1_wellord2(sK1) ),
    inference(subtyping,[status(esa)],[c_92])).

cnf(c_0,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( ~ v2_wellord1(X0)
    | v2_wellord1(k2_wellord1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_97,plain,
    ( ~ v2_wellord1(X0)
    | v2_wellord1(k2_wellord1(X0,X1))
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_98,plain,
    ( v2_wellord1(k2_wellord1(k1_wellord2(X0),X1))
    | ~ v2_wellord1(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_137,plain,
    ( v2_wellord1(k2_wellord1(k1_wellord2(X0_37),X1_37))
    | ~ v2_wellord1(k1_wellord2(X0_37)) ),
    inference(subtyping,[status(esa)],[c_98])).

cnf(c_209,plain,
    ( v2_wellord1(k2_wellord1(k1_wellord2(X0_37),X1_37)) = iProver_top
    | v2_wellord1(k1_wellord2(X0_37)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_291,plain,
    ( v2_wellord1(k1_wellord2(sK0)) != iProver_top
    | v2_wellord1(k1_wellord2(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_138,c_209])).

cnf(c_2,plain,
    ( ~ v3_ordinal1(X0)
    | v2_wellord1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_13,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( v3_ordinal1(sK0) != iProver_top
    | v2_wellord1(k1_wellord2(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4,negated_conjecture,
    ( ~ v2_wellord1(k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,plain,
    ( v2_wellord1(k1_wellord2(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,negated_conjecture,
    ( v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( v3_ordinal1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_291,c_15,c_9,c_7])).


%------------------------------------------------------------------------------
