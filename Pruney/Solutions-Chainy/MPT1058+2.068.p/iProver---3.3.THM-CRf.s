%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:22 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 285 expanded)
%              Number of clauses        :   61 ( 125 expanded)
%              Number of leaves         :   12 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  236 ( 699 expanded)
%              Number of equality atoms :  119 ( 297 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24])).

fof(f42,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_438,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_443,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1721,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_443])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_440,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_442,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1088,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_440,c_442])).

cnf(c_1725,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1721,c_1088])).

cnf(c_23,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5460,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1725,c_23])).

cnf(c_5461,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5460])).

cnf(c_5468,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_438,c_5461])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_446,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_987,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_440,c_446])).

cnf(c_6,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_992,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_987,c_6,c_7])).

cnf(c_12,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_439,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_996,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_439])).

cnf(c_997,plain,
    ( r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_996,c_7])).

cnf(c_10,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_46,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2152,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_23,c_26,c_46])).

cnf(c_4,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_445,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1383,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_445])).

cnf(c_1500,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1383,c_23])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_448,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1515,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_448])).

cnf(c_3611,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_1515])).

cnf(c_19732,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_438,c_3611])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_444,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2135,plain,
    ( k10_relat_1(X0,k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_440,c_444])).

cnf(c_3913,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(superposition,[status(thm)],[c_440,c_2135])).

cnf(c_3918,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_3913,c_1088])).

cnf(c_24338,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_19732,c_3918])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_436,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2136,plain,
    ( k10_relat_1(X0,k10_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(X0,sK0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_444])).

cnf(c_2668,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_440,c_2136])).

cnf(c_1089,plain,
    ( k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_436,c_442])).

cnf(c_2673,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2668,c_1089])).

cnf(c_24471,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k10_relat_1(k7_relat_1(sK0,X0),sK2) ),
    inference(demodulation,[status(thm)],[c_24338,c_2673])).

cnf(c_30631,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_5468,c_24471])).

cnf(c_30650,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_30631,c_19732])).

cnf(c_13,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_30661,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_30650,c_13])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1360,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1040,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),X0)
    | k10_relat_1(sK0,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1359,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30661,c_1360,c_1359])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:56:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.95/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.95/1.49  
% 7.95/1.49  ------  iProver source info
% 7.95/1.49  
% 7.95/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.95/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.95/1.49  git: non_committed_changes: false
% 7.95/1.49  git: last_make_outside_of_git: false
% 7.95/1.49  
% 7.95/1.49  ------ 
% 7.95/1.49  ------ Parsing...
% 7.95/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.95/1.49  
% 7.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.95/1.49  
% 7.95/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.95/1.49  
% 7.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.95/1.49  ------ Proving...
% 7.95/1.49  ------ Problem Properties 
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  clauses                                 16
% 7.95/1.49  conjectures                             4
% 7.95/1.49  EPR                                     4
% 7.95/1.49  Horn                                    16
% 7.95/1.49  unary                                   9
% 7.95/1.49  binary                                  3
% 7.95/1.49  lits                                    29
% 7.95/1.49  lits eq                                 8
% 7.95/1.49  fd_pure                                 0
% 7.95/1.49  fd_pseudo                               0
% 7.95/1.49  fd_cond                                 0
% 7.95/1.49  fd_pseudo_cond                          1
% 7.95/1.49  AC symbols                              0
% 7.95/1.49  
% 7.95/1.49  ------ Input Options Time Limit: Unbounded
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  ------ 
% 7.95/1.49  Current options:
% 7.95/1.49  ------ 
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  ------ Proving...
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  % SZS status Theorem for theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  fof(f10,conjecture,(
% 7.95/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f11,negated_conjecture,(
% 7.95/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.95/1.49    inference(negated_conjecture,[],[f10])).
% 7.95/1.49  
% 7.95/1.49  fof(f20,plain,(
% 7.95/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.95/1.49    inference(ennf_transformation,[],[f11])).
% 7.95/1.49  
% 7.95/1.49  fof(f21,plain,(
% 7.95/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.95/1.49    inference(flattening,[],[f20])).
% 7.95/1.49  
% 7.95/1.49  fof(f25,plain,(
% 7.95/1.49    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 7.95/1.49    introduced(choice_axiom,[])).
% 7.95/1.49  
% 7.95/1.49  fof(f24,plain,(
% 7.95/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 7.95/1.49    introduced(choice_axiom,[])).
% 7.95/1.49  
% 7.95/1.49  fof(f26,plain,(
% 7.95/1.49    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 7.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24])).
% 7.95/1.49  
% 7.95/1.49  fof(f42,plain,(
% 7.95/1.49    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 7.95/1.49    inference(cnf_transformation,[],[f26])).
% 7.95/1.49  
% 7.95/1.49  fof(f5,axiom,(
% 7.95/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f33,plain,(
% 7.95/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.95/1.49    inference(cnf_transformation,[],[f5])).
% 7.95/1.49  
% 7.95/1.49  fof(f6,axiom,(
% 7.95/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f15,plain,(
% 7.95/1.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.95/1.49    inference(ennf_transformation,[],[f6])).
% 7.95/1.49  
% 7.95/1.49  fof(f16,plain,(
% 7.95/1.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.95/1.49    inference(flattening,[],[f15])).
% 7.95/1.49  
% 7.95/1.49  fof(f35,plain,(
% 7.95/1.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f16])).
% 7.95/1.49  
% 7.95/1.49  fof(f8,axiom,(
% 7.95/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f37,plain,(
% 7.95/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.95/1.49    inference(cnf_transformation,[],[f8])).
% 7.95/1.49  
% 7.95/1.49  fof(f7,axiom,(
% 7.95/1.49    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f17,plain,(
% 7.95/1.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.95/1.49    inference(ennf_transformation,[],[f7])).
% 7.95/1.49  
% 7.95/1.49  fof(f36,plain,(
% 7.95/1.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f17])).
% 7.95/1.49  
% 7.95/1.49  fof(f2,axiom,(
% 7.95/1.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f12,plain,(
% 7.95/1.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.95/1.49    inference(ennf_transformation,[],[f2])).
% 7.95/1.49  
% 7.95/1.49  fof(f30,plain,(
% 7.95/1.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f12])).
% 7.95/1.49  
% 7.95/1.49  fof(f34,plain,(
% 7.95/1.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.95/1.49    inference(cnf_transformation,[],[f5])).
% 7.95/1.49  
% 7.95/1.49  fof(f9,axiom,(
% 7.95/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f18,plain,(
% 7.95/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.95/1.49    inference(ennf_transformation,[],[f9])).
% 7.95/1.49  
% 7.95/1.49  fof(f19,plain,(
% 7.95/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.95/1.49    inference(flattening,[],[f18])).
% 7.95/1.49  
% 7.95/1.49  fof(f39,plain,(
% 7.95/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f19])).
% 7.95/1.49  
% 7.95/1.49  fof(f38,plain,(
% 7.95/1.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.95/1.49    inference(cnf_transformation,[],[f8])).
% 7.95/1.49  
% 7.95/1.49  fof(f1,axiom,(
% 7.95/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f22,plain,(
% 7.95/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.95/1.49    inference(nnf_transformation,[],[f1])).
% 7.95/1.49  
% 7.95/1.49  fof(f23,plain,(
% 7.95/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.95/1.49    inference(flattening,[],[f22])).
% 7.95/1.49  
% 7.95/1.49  fof(f27,plain,(
% 7.95/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.95/1.49    inference(cnf_transformation,[],[f23])).
% 7.95/1.49  
% 7.95/1.49  fof(f45,plain,(
% 7.95/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.95/1.49    inference(equality_resolution,[],[f27])).
% 7.95/1.49  
% 7.95/1.49  fof(f3,axiom,(
% 7.95/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f13,plain,(
% 7.95/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.95/1.49    inference(ennf_transformation,[],[f3])).
% 7.95/1.49  
% 7.95/1.49  fof(f31,plain,(
% 7.95/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f13])).
% 7.95/1.49  
% 7.95/1.49  fof(f29,plain,(
% 7.95/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f23])).
% 7.95/1.49  
% 7.95/1.49  fof(f4,axiom,(
% 7.95/1.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 7.95/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.49  
% 7.95/1.49  fof(f14,plain,(
% 7.95/1.49    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.95/1.49    inference(ennf_transformation,[],[f4])).
% 7.95/1.49  
% 7.95/1.49  fof(f32,plain,(
% 7.95/1.49    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 7.95/1.49    inference(cnf_transformation,[],[f14])).
% 7.95/1.49  
% 7.95/1.49  fof(f40,plain,(
% 7.95/1.49    v1_relat_1(sK0)),
% 7.95/1.49    inference(cnf_transformation,[],[f26])).
% 7.95/1.49  
% 7.95/1.49  fof(f43,plain,(
% 7.95/1.49    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 7.95/1.49    inference(cnf_transformation,[],[f26])).
% 7.95/1.49  
% 7.95/1.49  fof(f28,plain,(
% 7.95/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.95/1.49    inference(cnf_transformation,[],[f23])).
% 7.95/1.49  
% 7.95/1.49  fof(f44,plain,(
% 7.95/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.95/1.49    inference(equality_resolution,[],[f28])).
% 7.95/1.49  
% 7.95/1.49  cnf(c_14,negated_conjecture,
% 7.95/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_438,plain,
% 7.95/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_7,plain,
% 7.95/1.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.95/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_8,plain,
% 7.95/1.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.95/1.49      | ~ v1_relat_1(X0)
% 7.95/1.49      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 7.95/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_443,plain,
% 7.95/1.49      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 7.95/1.49      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.95/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1721,plain,
% 7.95/1.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X1)
% 7.95/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.95/1.49      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_7,c_443]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_11,plain,
% 7.95/1.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.95/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_440,plain,
% 7.95/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_9,plain,
% 7.95/1.49      ( ~ v1_relat_1(X0)
% 7.95/1.49      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_442,plain,
% 7.95/1.49      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.95/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1088,plain,
% 7.95/1.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_440,c_442]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1725,plain,
% 7.95/1.49      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.95/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.95/1.49      inference(demodulation,[status(thm)],[c_1721,c_1088]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_23,plain,
% 7.95/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_5460,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 7.95/1.49      inference(global_propositional_subsumption,
% 7.95/1.49                [status(thm)],
% 7.95/1.49                [c_1725,c_23]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_5461,plain,
% 7.95/1.49      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.95/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.95/1.49      inference(renaming,[status(thm)],[c_5460]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_5468,plain,
% 7.95/1.49      ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_438,c_5461]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_3,plain,
% 7.95/1.49      ( ~ v1_relat_1(X0)
% 7.95/1.49      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_446,plain,
% 7.95/1.49      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 7.95/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_987,plain,
% 7.95/1.49      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_440,c_446]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_6,plain,
% 7.95/1.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.95/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_992,plain,
% 7.95/1.49      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 7.95/1.49      inference(light_normalisation,[status(thm)],[c_987,c_6,c_7]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_12,plain,
% 7.95/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.95/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.95/1.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.95/1.49      | ~ v1_funct_1(X1)
% 7.95/1.49      | ~ v1_relat_1(X1) ),
% 7.95/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_439,plain,
% 7.95/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 7.95/1.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.95/1.49      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 7.95/1.49      | v1_funct_1(X1) != iProver_top
% 7.95/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_996,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.95/1.49      | r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) != iProver_top
% 7.95/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.95/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_992,c_439]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_997,plain,
% 7.95/1.49      ( r1_tarski(X0,X0) != iProver_top
% 7.95/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.95/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.95/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.95/1.49      inference(light_normalisation,[status(thm)],[c_996,c_7]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_10,plain,
% 7.95/1.49      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.95/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_26,plain,
% 7.95/1.49      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2,plain,
% 7.95/1.49      ( r1_tarski(X0,X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_46,plain,
% 7.95/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2152,plain,
% 7.95/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 7.95/1.49      inference(global_propositional_subsumption,
% 7.95/1.49                [status(thm)],
% 7.95/1.49                [c_997,c_23,c_26,c_46]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_4,plain,
% 7.95/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_445,plain,
% 7.95/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.95/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1383,plain,
% 7.95/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 7.95/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_7,c_445]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1500,plain,
% 7.95/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 7.95/1.49      inference(global_propositional_subsumption,
% 7.95/1.49                [status(thm)],
% 7.95/1.49                [c_1383,c_23]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_0,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.95/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_448,plain,
% 7.95/1.49      ( X0 = X1
% 7.95/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.95/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1515,plain,
% 7.95/1.49      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 7.95/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_1500,c_448]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_3611,plain,
% 7.95/1.49      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 7.95/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_2152,c_1515]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_19732,plain,
% 7.95/1.49      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_438,c_3611]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_5,plain,
% 7.95/1.49      ( ~ v1_relat_1(X0)
% 7.95/1.49      | ~ v1_relat_1(X1)
% 7.95/1.49      | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
% 7.95/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_444,plain,
% 7.95/1.49      ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
% 7.95/1.49      | v1_relat_1(X1) != iProver_top
% 7.95/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2135,plain,
% 7.95/1.49      ( k10_relat_1(X0,k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k5_relat_1(X0,k6_relat_1(X1)),X2)
% 7.95/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_440,c_444]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_3913,plain,
% 7.95/1.49      ( k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_440,c_2135]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_3918,plain,
% 7.95/1.49      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 7.95/1.49      inference(light_normalisation,[status(thm)],[c_3913,c_1088]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_24338,plain,
% 7.95/1.49      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2)) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_19732,c_3918]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_16,negated_conjecture,
% 7.95/1.49      ( v1_relat_1(sK0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_436,plain,
% 7.95/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 7.95/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2136,plain,
% 7.95/1.49      ( k10_relat_1(X0,k10_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(X0,sK0),X1)
% 7.95/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_436,c_444]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2668,plain,
% 7.95/1.49      ( k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_440,c_2136]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1089,plain,
% 7.95/1.49      ( k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_436,c_442]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_2673,plain,
% 7.95/1.49      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 7.95/1.49      inference(light_normalisation,[status(thm)],[c_2668,c_1089]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_24471,plain,
% 7.95/1.49      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),sK1) = k10_relat_1(k7_relat_1(sK0,X0),sK2) ),
% 7.95/1.49      inference(demodulation,[status(thm)],[c_24338,c_2673]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_30631,plain,
% 7.95/1.49      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.95/1.49      inference(superposition,[status(thm)],[c_5468,c_24471]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_30650,plain,
% 7.95/1.49      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 7.95/1.49      inference(light_normalisation,[status(thm)],[c_30631,c_19732]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_13,negated_conjecture,
% 7.95/1.49      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.95/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_30661,plain,
% 7.95/1.49      ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 7.95/1.49      inference(demodulation,[status(thm)],[c_30650,c_13]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1,plain,
% 7.95/1.49      ( r1_tarski(X0,X0) ),
% 7.95/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1360,plain,
% 7.95/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1040,plain,
% 7.95/1.49      ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
% 7.95/1.49      | ~ r1_tarski(k10_relat_1(sK0,sK2),X0)
% 7.95/1.49      | k10_relat_1(sK0,sK2) = X0 ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(c_1359,plain,
% 7.95/1.49      ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
% 7.95/1.49      | k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 7.95/1.49      inference(instantiation,[status(thm)],[c_1040]) ).
% 7.95/1.49  
% 7.95/1.49  cnf(contradiction,plain,
% 7.95/1.49      ( $false ),
% 7.95/1.49      inference(minisat,[status(thm)],[c_30661,c_1360,c_1359]) ).
% 7.95/1.49  
% 7.95/1.49  
% 7.95/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.95/1.49  
% 7.95/1.49  ------                               Statistics
% 7.95/1.49  
% 7.95/1.49  ------ Selected
% 7.95/1.49  
% 7.95/1.49  total_time:                             0.963
% 7.95/1.49  
%------------------------------------------------------------------------------
