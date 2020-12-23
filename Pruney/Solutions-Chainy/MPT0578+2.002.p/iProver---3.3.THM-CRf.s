%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:52 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 224 expanded)
%              Number of clauses        :   57 ( 102 expanded)
%              Number of leaves         :   12 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  188 ( 553 expanded)
%              Number of equality atoms :   90 ( 229 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
     => ( k10_relat_1(X0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(X0,sK1))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k10_relat_1(sK0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(sK0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_88,plain,
    ( r1_tarski(k10_relat_1(X0_37,X0_38),k1_relat_1(X0_37))
    | ~ v1_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_236,plain,
    ( r1_tarski(k10_relat_1(X0_37,X0_38),k1_relat_1(X0_37)) = iProver_top
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_83,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_240,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_82,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_241,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_89,plain,
    ( ~ v1_relat_1(X0_37)
    | ~ v1_relat_1(X1_37)
    | v1_relat_1(k5_relat_1(X1_37,X0_37)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_235,plain,
    ( v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top
    | v1_relat_1(k5_relat_1(X1_37,X0_37)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_89])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_87,plain,
    ( ~ v1_relat_1(X0_37)
    | k10_relat_1(X0_37,k2_relat_1(X0_37)) = k1_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_237,plain,
    ( k10_relat_1(X0_37,k2_relat_1(X0_37)) = k1_relat_1(X0_37)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_590,plain,
    ( k10_relat_1(k5_relat_1(X0_37,X1_37),k2_relat_1(k5_relat_1(X0_37,X1_37))) = k1_relat_1(k5_relat_1(X0_37,X1_37))
    | v1_relat_1(X1_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_235,c_237])).

cnf(c_1352,plain,
    ( k10_relat_1(k5_relat_1(sK0,X0_37),k2_relat_1(k5_relat_1(sK0,X0_37))) = k1_relat_1(k5_relat_1(sK0,X0_37))
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_241,c_590])).

cnf(c_3569,plain,
    ( k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_240,c_1352])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_85,plain,
    ( ~ v1_relat_1(X0_37)
    | ~ v1_relat_1(X1_37)
    | k10_relat_1(k5_relat_1(X0_37,X1_37),X0_38) = k10_relat_1(X0_37,k10_relat_1(X1_37,X0_38)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_239,plain,
    ( k10_relat_1(k5_relat_1(X0_37,X1_37),X0_38) = k10_relat_1(X0_37,k10_relat_1(X1_37,X0_38))
    | v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_719,plain,
    ( k10_relat_1(sK0,k10_relat_1(X0_37,X0_38)) = k10_relat_1(k5_relat_1(sK0,X0_37),X0_38)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_241,c_239])).

cnf(c_2623,plain,
    ( k10_relat_1(sK0,k10_relat_1(sK1,X0_38)) = k10_relat_1(k5_relat_1(sK0,sK1),X0_38) ),
    inference(superposition,[status(thm)],[c_240,c_719])).

cnf(c_3944,plain,
    ( k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3569,c_2623])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_86,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k10_relat_1(X0_37,X0_38),k10_relat_1(X0_37,X1_38))
    | ~ v1_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_238,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(k10_relat_1(X0_37,X0_38),k10_relat_1(X0_37,X1_38)) = iProver_top
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_24518,plain,
    ( r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X0_38) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X0_38)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_238])).

cnf(c_10,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_29013,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X0_38)) = iProver_top
    | r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X0_38) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24518,c_10])).

cnf(c_29014,plain,
    ( r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X0_38) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X0_38)) = iProver_top ),
    inference(renaming,[status(thm)],[c_29013])).

cnf(c_29022,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_236,c_29014])).

cnf(c_588,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_240,c_237])).

cnf(c_2807,plain,
    ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0_38)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2623,c_236])).

cnf(c_11,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_659,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_660,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_6449,plain,
    ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0_38)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2807,c_10,c_11,c_660])).

cnf(c_6456,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_6449])).

cnf(c_94,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_93,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_626,plain,
    ( X0_38 != X1_38
    | X1_38 = X0_38 ),
    inference(resolution,[status(thm)],[c_94,c_93])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_90,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | k3_xboole_0(X0_38,X1_38) = X0_38 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_637,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | X0_38 = k3_xboole_0(X0_38,X1_38) ),
    inference(resolution,[status(thm)],[c_626,c_90])).

cnf(c_651,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | X0_38 = X2_38
    | X2_38 != k3_xboole_0(X0_38,X1_38) ),
    inference(resolution,[status(thm)],[c_637,c_94])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_91,plain,
    ( k3_xboole_0(X0_38,X1_38) = k3_xboole_0(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_624,plain,
    ( X0_38 != k3_xboole_0(X1_38,X2_38)
    | k3_xboole_0(X2_38,X1_38) = X0_38 ),
    inference(resolution,[status(thm)],[c_94,c_91])).

cnf(c_1185,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | k3_xboole_0(X1_38,X0_38) = X0_38 ),
    inference(resolution,[status(thm)],[c_624,c_637])).

cnf(c_1193,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | X0_38 = k3_xboole_0(X1_38,X0_38) ),
    inference(resolution,[status(thm)],[c_1185,c_626])).

cnf(c_1754,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X1_38,X0_38)
    | X0_38 = X1_38 ),
    inference(resolution,[status(thm)],[c_651,c_1193])).

cnf(c_7,negated_conjecture,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_84,negated_conjecture,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2013,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[status(thm)],[c_1754,c_84])).

cnf(c_2014,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29022,c_6456,c_2014,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.89/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.50  
% 7.89/1.50  ------  iProver source info
% 7.89/1.50  
% 7.89/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.50  git: non_committed_changes: false
% 7.89/1.50  git: last_make_outside_of_git: false
% 7.89/1.50  
% 7.89/1.50  ------ 
% 7.89/1.50  
% 7.89/1.50  ------ Input Options
% 7.89/1.50  
% 7.89/1.50  --out_options                           all
% 7.89/1.50  --tptp_safe_out                         true
% 7.89/1.50  --problem_path                          ""
% 7.89/1.50  --include_path                          ""
% 7.89/1.50  --clausifier                            res/vclausify_rel
% 7.89/1.50  --clausifier_options                    --mode clausify
% 7.89/1.50  --stdin                                 false
% 7.89/1.50  --stats_out                             sel
% 7.89/1.50  
% 7.89/1.50  ------ General Options
% 7.89/1.50  
% 7.89/1.50  --fof                                   false
% 7.89/1.50  --time_out_real                         604.99
% 7.89/1.50  --time_out_virtual                      -1.
% 7.89/1.50  --symbol_type_check                     false
% 7.89/1.50  --clausify_out                          false
% 7.89/1.50  --sig_cnt_out                           false
% 7.89/1.50  --trig_cnt_out                          false
% 7.89/1.50  --trig_cnt_out_tolerance                1.
% 7.89/1.50  --trig_cnt_out_sk_spl                   false
% 7.89/1.50  --abstr_cl_out                          false
% 7.89/1.50  
% 7.89/1.50  ------ Global Options
% 7.89/1.50  
% 7.89/1.50  --schedule                              none
% 7.89/1.50  --add_important_lit                     false
% 7.89/1.50  --prop_solver_per_cl                    1000
% 7.89/1.50  --min_unsat_core                        false
% 7.89/1.50  --soft_assumptions                      false
% 7.89/1.50  --soft_lemma_size                       3
% 7.89/1.50  --prop_impl_unit_size                   0
% 7.89/1.50  --prop_impl_unit                        []
% 7.89/1.50  --share_sel_clauses                     true
% 7.89/1.50  --reset_solvers                         false
% 7.89/1.50  --bc_imp_inh                            [conj_cone]
% 7.89/1.50  --conj_cone_tolerance                   3.
% 7.89/1.50  --extra_neg_conj                        none
% 7.89/1.50  --large_theory_mode                     true
% 7.89/1.50  --prolific_symb_bound                   200
% 7.89/1.50  --lt_threshold                          2000
% 7.89/1.50  --clause_weak_htbl                      true
% 7.89/1.50  --gc_record_bc_elim                     false
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing Options
% 7.89/1.50  
% 7.89/1.50  --preprocessing_flag                    true
% 7.89/1.50  --time_out_prep_mult                    0.1
% 7.89/1.50  --splitting_mode                        input
% 7.89/1.50  --splitting_grd                         true
% 7.89/1.50  --splitting_cvd                         false
% 7.89/1.50  --splitting_cvd_svl                     false
% 7.89/1.50  --splitting_nvd                         32
% 7.89/1.50  --sub_typing                            true
% 7.89/1.50  --prep_gs_sim                           false
% 7.89/1.50  --prep_unflatten                        true
% 7.89/1.50  --prep_res_sim                          true
% 7.89/1.50  --prep_upred                            true
% 7.89/1.50  --prep_sem_filter                       exhaustive
% 7.89/1.50  --prep_sem_filter_out                   false
% 7.89/1.50  --pred_elim                             false
% 7.89/1.50  --res_sim_input                         true
% 7.89/1.50  --eq_ax_congr_red                       true
% 7.89/1.50  --pure_diseq_elim                       true
% 7.89/1.50  --brand_transform                       false
% 7.89/1.50  --non_eq_to_eq                          false
% 7.89/1.50  --prep_def_merge                        true
% 7.89/1.50  --prep_def_merge_prop_impl              false
% 7.89/1.50  --prep_def_merge_mbd                    true
% 7.89/1.50  --prep_def_merge_tr_red                 false
% 7.89/1.50  --prep_def_merge_tr_cl                  false
% 7.89/1.50  --smt_preprocessing                     true
% 7.89/1.50  --smt_ac_axioms                         fast
% 7.89/1.50  --preprocessed_out                      false
% 7.89/1.50  --preprocessed_stats                    false
% 7.89/1.50  
% 7.89/1.50  ------ Abstraction refinement Options
% 7.89/1.50  
% 7.89/1.50  --abstr_ref                             []
% 7.89/1.50  --abstr_ref_prep                        false
% 7.89/1.50  --abstr_ref_until_sat                   false
% 7.89/1.50  --abstr_ref_sig_restrict                funpre
% 7.89/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.50  --abstr_ref_under                       []
% 7.89/1.50  
% 7.89/1.50  ------ SAT Options
% 7.89/1.50  
% 7.89/1.50  --sat_mode                              false
% 7.89/1.50  --sat_fm_restart_options                ""
% 7.89/1.50  --sat_gr_def                            false
% 7.89/1.50  --sat_epr_types                         true
% 7.89/1.50  --sat_non_cyclic_types                  false
% 7.89/1.50  --sat_finite_models                     false
% 7.89/1.50  --sat_fm_lemmas                         false
% 7.89/1.50  --sat_fm_prep                           false
% 7.89/1.50  --sat_fm_uc_incr                        true
% 7.89/1.50  --sat_out_model                         small
% 7.89/1.50  --sat_out_clauses                       false
% 7.89/1.50  
% 7.89/1.50  ------ QBF Options
% 7.89/1.50  
% 7.89/1.50  --qbf_mode                              false
% 7.89/1.50  --qbf_elim_univ                         false
% 7.89/1.50  --qbf_dom_inst                          none
% 7.89/1.50  --qbf_dom_pre_inst                      false
% 7.89/1.50  --qbf_sk_in                             false
% 7.89/1.50  --qbf_pred_elim                         true
% 7.89/1.50  --qbf_split                             512
% 7.89/1.50  
% 7.89/1.50  ------ BMC1 Options
% 7.89/1.50  
% 7.89/1.50  --bmc1_incremental                      false
% 7.89/1.50  --bmc1_axioms                           reachable_all
% 7.89/1.50  --bmc1_min_bound                        0
% 7.89/1.50  --bmc1_max_bound                        -1
% 7.89/1.50  --bmc1_max_bound_default                -1
% 7.89/1.50  --bmc1_symbol_reachability              true
% 7.89/1.50  --bmc1_property_lemmas                  false
% 7.89/1.50  --bmc1_k_induction                      false
% 7.89/1.50  --bmc1_non_equiv_states                 false
% 7.89/1.50  --bmc1_deadlock                         false
% 7.89/1.50  --bmc1_ucm                              false
% 7.89/1.50  --bmc1_add_unsat_core                   none
% 7.89/1.50  --bmc1_unsat_core_children              false
% 7.89/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.50  --bmc1_out_stat                         full
% 7.89/1.50  --bmc1_ground_init                      false
% 7.89/1.50  --bmc1_pre_inst_next_state              false
% 7.89/1.50  --bmc1_pre_inst_state                   false
% 7.89/1.50  --bmc1_pre_inst_reach_state             false
% 7.89/1.50  --bmc1_out_unsat_core                   false
% 7.89/1.50  --bmc1_aig_witness_out                  false
% 7.89/1.50  --bmc1_verbose                          false
% 7.89/1.50  --bmc1_dump_clauses_tptp                false
% 7.89/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.50  --bmc1_dump_file                        -
% 7.89/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.50  --bmc1_ucm_extend_mode                  1
% 7.89/1.50  --bmc1_ucm_init_mode                    2
% 7.89/1.50  --bmc1_ucm_cone_mode                    none
% 7.89/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.50  --bmc1_ucm_relax_model                  4
% 7.89/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.50  --bmc1_ucm_layered_model                none
% 7.89/1.50  --bmc1_ucm_max_lemma_size               10
% 7.89/1.50  
% 7.89/1.50  ------ AIG Options
% 7.89/1.50  
% 7.89/1.50  --aig_mode                              false
% 7.89/1.50  
% 7.89/1.50  ------ Instantiation Options
% 7.89/1.50  
% 7.89/1.50  --instantiation_flag                    true
% 7.89/1.50  --inst_sos_flag                         false
% 7.89/1.50  --inst_sos_phase                        true
% 7.89/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.50  --inst_lit_sel_side                     num_symb
% 7.89/1.50  --inst_solver_per_active                1400
% 7.89/1.50  --inst_solver_calls_frac                1.
% 7.89/1.50  --inst_passive_queue_type               priority_queues
% 7.89/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.50  --inst_passive_queues_freq              [25;2]
% 7.89/1.50  --inst_dismatching                      true
% 7.89/1.50  --inst_eager_unprocessed_to_passive     true
% 7.89/1.50  --inst_prop_sim_given                   true
% 7.89/1.50  --inst_prop_sim_new                     false
% 7.89/1.50  --inst_subs_new                         false
% 7.89/1.50  --inst_eq_res_simp                      false
% 7.89/1.50  --inst_subs_given                       false
% 7.89/1.50  --inst_orphan_elimination               true
% 7.89/1.50  --inst_learning_loop_flag               true
% 7.89/1.50  --inst_learning_start                   3000
% 7.89/1.50  --inst_learning_factor                  2
% 7.89/1.50  --inst_start_prop_sim_after_learn       3
% 7.89/1.50  --inst_sel_renew                        solver
% 7.89/1.50  --inst_lit_activity_flag                true
% 7.89/1.50  --inst_restr_to_given                   false
% 7.89/1.50  --inst_activity_threshold               500
% 7.89/1.50  --inst_out_proof                        true
% 7.89/1.50  
% 7.89/1.50  ------ Resolution Options
% 7.89/1.50  
% 7.89/1.50  --resolution_flag                       true
% 7.89/1.50  --res_lit_sel                           adaptive
% 7.89/1.50  --res_lit_sel_side                      none
% 7.89/1.50  --res_ordering                          kbo
% 7.89/1.50  --res_to_prop_solver                    active
% 7.89/1.50  --res_prop_simpl_new                    false
% 7.89/1.50  --res_prop_simpl_given                  true
% 7.89/1.50  --res_passive_queue_type                priority_queues
% 7.89/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.50  --res_passive_queues_freq               [15;5]
% 7.89/1.50  --res_forward_subs                      full
% 7.89/1.50  --res_backward_subs                     full
% 7.89/1.50  --res_forward_subs_resolution           true
% 7.89/1.50  --res_backward_subs_resolution          true
% 7.89/1.50  --res_orphan_elimination                true
% 7.89/1.50  --res_time_limit                        2.
% 7.89/1.50  --res_out_proof                         true
% 7.89/1.50  
% 7.89/1.50  ------ Superposition Options
% 7.89/1.50  
% 7.89/1.50  --superposition_flag                    true
% 7.89/1.50  --sup_passive_queue_type                priority_queues
% 7.89/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.50  --sup_passive_queues_freq               [1;4]
% 7.89/1.50  --demod_completeness_check              fast
% 7.89/1.50  --demod_use_ground                      true
% 7.89/1.50  --sup_to_prop_solver                    passive
% 7.89/1.50  --sup_prop_simpl_new                    true
% 7.89/1.50  --sup_prop_simpl_given                  true
% 7.89/1.50  --sup_fun_splitting                     false
% 7.89/1.50  --sup_smt_interval                      50000
% 7.89/1.50  
% 7.89/1.50  ------ Superposition Simplification Setup
% 7.89/1.50  
% 7.89/1.50  --sup_indices_passive                   []
% 7.89/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.50  --sup_full_bw                           [BwDemod]
% 7.89/1.50  --sup_immed_triv                        [TrivRules]
% 7.89/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.50  --sup_immed_bw_main                     []
% 7.89/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.50  
% 7.89/1.50  ------ Combination Options
% 7.89/1.50  
% 7.89/1.50  --comb_res_mult                         3
% 7.89/1.50  --comb_sup_mult                         2
% 7.89/1.50  --comb_inst_mult                        10
% 7.89/1.50  
% 7.89/1.50  ------ Debug Options
% 7.89/1.50  
% 7.89/1.50  --dbg_backtrace                         false
% 7.89/1.50  --dbg_dump_prop_clauses                 false
% 7.89/1.50  --dbg_dump_prop_clauses_file            -
% 7.89/1.50  --dbg_out_stat                          false
% 7.89/1.50  ------ Parsing...
% 7.89/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.50  ------ Proving...
% 7.89/1.50  ------ Problem Properties 
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  clauses                                 10
% 7.89/1.50  conjectures                             3
% 7.89/1.50  EPR                                     2
% 7.89/1.50  Horn                                    10
% 7.89/1.50  unary                                   4
% 7.89/1.50  binary                                  3
% 7.89/1.50  lits                                    19
% 7.89/1.50  lits eq                                 5
% 7.89/1.50  fd_pure                                 0
% 7.89/1.50  fd_pseudo                               0
% 7.89/1.50  fd_cond                                 0
% 7.89/1.50  fd_pseudo_cond                          0
% 7.89/1.50  AC symbols                              0
% 7.89/1.50  
% 7.89/1.50  ------ Input Options Time Limit: Unbounded
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  ------ 
% 7.89/1.50  Current options:
% 7.89/1.50  ------ 
% 7.89/1.50  
% 7.89/1.50  ------ Input Options
% 7.89/1.50  
% 7.89/1.50  --out_options                           all
% 7.89/1.50  --tptp_safe_out                         true
% 7.89/1.50  --problem_path                          ""
% 7.89/1.50  --include_path                          ""
% 7.89/1.50  --clausifier                            res/vclausify_rel
% 7.89/1.50  --clausifier_options                    --mode clausify
% 7.89/1.50  --stdin                                 false
% 7.89/1.50  --stats_out                             sel
% 7.89/1.50  
% 7.89/1.50  ------ General Options
% 7.89/1.50  
% 7.89/1.50  --fof                                   false
% 7.89/1.50  --time_out_real                         604.99
% 7.89/1.50  --time_out_virtual                      -1.
% 7.89/1.50  --symbol_type_check                     false
% 7.89/1.50  --clausify_out                          false
% 7.89/1.50  --sig_cnt_out                           false
% 7.89/1.50  --trig_cnt_out                          false
% 7.89/1.50  --trig_cnt_out_tolerance                1.
% 7.89/1.50  --trig_cnt_out_sk_spl                   false
% 7.89/1.50  --abstr_cl_out                          false
% 7.89/1.50  
% 7.89/1.50  ------ Global Options
% 7.89/1.50  
% 7.89/1.50  --schedule                              none
% 7.89/1.50  --add_important_lit                     false
% 7.89/1.50  --prop_solver_per_cl                    1000
% 7.89/1.50  --min_unsat_core                        false
% 7.89/1.50  --soft_assumptions                      false
% 7.89/1.50  --soft_lemma_size                       3
% 7.89/1.50  --prop_impl_unit_size                   0
% 7.89/1.50  --prop_impl_unit                        []
% 7.89/1.50  --share_sel_clauses                     true
% 7.89/1.50  --reset_solvers                         false
% 7.89/1.50  --bc_imp_inh                            [conj_cone]
% 7.89/1.50  --conj_cone_tolerance                   3.
% 7.89/1.50  --extra_neg_conj                        none
% 7.89/1.50  --large_theory_mode                     true
% 7.89/1.50  --prolific_symb_bound                   200
% 7.89/1.50  --lt_threshold                          2000
% 7.89/1.50  --clause_weak_htbl                      true
% 7.89/1.50  --gc_record_bc_elim                     false
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing Options
% 7.89/1.50  
% 7.89/1.50  --preprocessing_flag                    true
% 7.89/1.50  --time_out_prep_mult                    0.1
% 7.89/1.50  --splitting_mode                        input
% 7.89/1.50  --splitting_grd                         true
% 7.89/1.50  --splitting_cvd                         false
% 7.89/1.50  --splitting_cvd_svl                     false
% 7.89/1.50  --splitting_nvd                         32
% 7.89/1.50  --sub_typing                            true
% 7.89/1.50  --prep_gs_sim                           false
% 7.89/1.50  --prep_unflatten                        true
% 7.89/1.50  --prep_res_sim                          true
% 7.89/1.50  --prep_upred                            true
% 7.89/1.50  --prep_sem_filter                       exhaustive
% 7.89/1.50  --prep_sem_filter_out                   false
% 7.89/1.50  --pred_elim                             false
% 7.89/1.50  --res_sim_input                         true
% 7.89/1.50  --eq_ax_congr_red                       true
% 7.89/1.50  --pure_diseq_elim                       true
% 7.89/1.50  --brand_transform                       false
% 7.89/1.50  --non_eq_to_eq                          false
% 7.89/1.50  --prep_def_merge                        true
% 7.89/1.50  --prep_def_merge_prop_impl              false
% 7.89/1.50  --prep_def_merge_mbd                    true
% 7.89/1.50  --prep_def_merge_tr_red                 false
% 7.89/1.50  --prep_def_merge_tr_cl                  false
% 7.89/1.50  --smt_preprocessing                     true
% 7.89/1.50  --smt_ac_axioms                         fast
% 7.89/1.50  --preprocessed_out                      false
% 7.89/1.50  --preprocessed_stats                    false
% 7.89/1.50  
% 7.89/1.50  ------ Abstraction refinement Options
% 7.89/1.50  
% 7.89/1.50  --abstr_ref                             []
% 7.89/1.50  --abstr_ref_prep                        false
% 7.89/1.50  --abstr_ref_until_sat                   false
% 7.89/1.50  --abstr_ref_sig_restrict                funpre
% 7.89/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.50  --abstr_ref_under                       []
% 7.89/1.50  
% 7.89/1.50  ------ SAT Options
% 7.89/1.50  
% 7.89/1.50  --sat_mode                              false
% 7.89/1.50  --sat_fm_restart_options                ""
% 7.89/1.50  --sat_gr_def                            false
% 7.89/1.50  --sat_epr_types                         true
% 7.89/1.50  --sat_non_cyclic_types                  false
% 7.89/1.50  --sat_finite_models                     false
% 7.89/1.50  --sat_fm_lemmas                         false
% 7.89/1.50  --sat_fm_prep                           false
% 7.89/1.50  --sat_fm_uc_incr                        true
% 7.89/1.50  --sat_out_model                         small
% 7.89/1.50  --sat_out_clauses                       false
% 7.89/1.50  
% 7.89/1.50  ------ QBF Options
% 7.89/1.50  
% 7.89/1.50  --qbf_mode                              false
% 7.89/1.50  --qbf_elim_univ                         false
% 7.89/1.50  --qbf_dom_inst                          none
% 7.89/1.50  --qbf_dom_pre_inst                      false
% 7.89/1.50  --qbf_sk_in                             false
% 7.89/1.50  --qbf_pred_elim                         true
% 7.89/1.50  --qbf_split                             512
% 7.89/1.50  
% 7.89/1.50  ------ BMC1 Options
% 7.89/1.50  
% 7.89/1.50  --bmc1_incremental                      false
% 7.89/1.50  --bmc1_axioms                           reachable_all
% 7.89/1.50  --bmc1_min_bound                        0
% 7.89/1.50  --bmc1_max_bound                        -1
% 7.89/1.50  --bmc1_max_bound_default                -1
% 7.89/1.50  --bmc1_symbol_reachability              true
% 7.89/1.50  --bmc1_property_lemmas                  false
% 7.89/1.50  --bmc1_k_induction                      false
% 7.89/1.50  --bmc1_non_equiv_states                 false
% 7.89/1.50  --bmc1_deadlock                         false
% 7.89/1.50  --bmc1_ucm                              false
% 7.89/1.50  --bmc1_add_unsat_core                   none
% 7.89/1.50  --bmc1_unsat_core_children              false
% 7.89/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.50  --bmc1_out_stat                         full
% 7.89/1.50  --bmc1_ground_init                      false
% 7.89/1.50  --bmc1_pre_inst_next_state              false
% 7.89/1.50  --bmc1_pre_inst_state                   false
% 7.89/1.50  --bmc1_pre_inst_reach_state             false
% 7.89/1.50  --bmc1_out_unsat_core                   false
% 7.89/1.50  --bmc1_aig_witness_out                  false
% 7.89/1.50  --bmc1_verbose                          false
% 7.89/1.50  --bmc1_dump_clauses_tptp                false
% 7.89/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.50  --bmc1_dump_file                        -
% 7.89/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.50  --bmc1_ucm_extend_mode                  1
% 7.89/1.50  --bmc1_ucm_init_mode                    2
% 7.89/1.50  --bmc1_ucm_cone_mode                    none
% 7.89/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.50  --bmc1_ucm_relax_model                  4
% 7.89/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.50  --bmc1_ucm_layered_model                none
% 7.89/1.50  --bmc1_ucm_max_lemma_size               10
% 7.89/1.50  
% 7.89/1.50  ------ AIG Options
% 7.89/1.50  
% 7.89/1.50  --aig_mode                              false
% 7.89/1.50  
% 7.89/1.50  ------ Instantiation Options
% 7.89/1.50  
% 7.89/1.50  --instantiation_flag                    true
% 7.89/1.50  --inst_sos_flag                         false
% 7.89/1.50  --inst_sos_phase                        true
% 7.89/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.50  --inst_lit_sel_side                     num_symb
% 7.89/1.50  --inst_solver_per_active                1400
% 7.89/1.50  --inst_solver_calls_frac                1.
% 7.89/1.50  --inst_passive_queue_type               priority_queues
% 7.89/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.50  --inst_passive_queues_freq              [25;2]
% 7.89/1.50  --inst_dismatching                      true
% 7.89/1.50  --inst_eager_unprocessed_to_passive     true
% 7.89/1.50  --inst_prop_sim_given                   true
% 7.89/1.50  --inst_prop_sim_new                     false
% 7.89/1.50  --inst_subs_new                         false
% 7.89/1.50  --inst_eq_res_simp                      false
% 7.89/1.50  --inst_subs_given                       false
% 7.89/1.50  --inst_orphan_elimination               true
% 7.89/1.50  --inst_learning_loop_flag               true
% 7.89/1.50  --inst_learning_start                   3000
% 7.89/1.50  --inst_learning_factor                  2
% 7.89/1.50  --inst_start_prop_sim_after_learn       3
% 7.89/1.50  --inst_sel_renew                        solver
% 7.89/1.50  --inst_lit_activity_flag                true
% 7.89/1.50  --inst_restr_to_given                   false
% 7.89/1.50  --inst_activity_threshold               500
% 7.89/1.50  --inst_out_proof                        true
% 7.89/1.50  
% 7.89/1.50  ------ Resolution Options
% 7.89/1.50  
% 7.89/1.50  --resolution_flag                       true
% 7.89/1.50  --res_lit_sel                           adaptive
% 7.89/1.50  --res_lit_sel_side                      none
% 7.89/1.50  --res_ordering                          kbo
% 7.89/1.50  --res_to_prop_solver                    active
% 7.89/1.50  --res_prop_simpl_new                    false
% 7.89/1.50  --res_prop_simpl_given                  true
% 7.89/1.50  --res_passive_queue_type                priority_queues
% 7.89/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.50  --res_passive_queues_freq               [15;5]
% 7.89/1.50  --res_forward_subs                      full
% 7.89/1.50  --res_backward_subs                     full
% 7.89/1.50  --res_forward_subs_resolution           true
% 7.89/1.50  --res_backward_subs_resolution          true
% 7.89/1.50  --res_orphan_elimination                true
% 7.89/1.50  --res_time_limit                        2.
% 7.89/1.50  --res_out_proof                         true
% 7.89/1.50  
% 7.89/1.50  ------ Superposition Options
% 7.89/1.50  
% 7.89/1.50  --superposition_flag                    true
% 7.89/1.50  --sup_passive_queue_type                priority_queues
% 7.89/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.50  --sup_passive_queues_freq               [1;4]
% 7.89/1.50  --demod_completeness_check              fast
% 7.89/1.50  --demod_use_ground                      true
% 7.89/1.50  --sup_to_prop_solver                    passive
% 7.89/1.50  --sup_prop_simpl_new                    true
% 7.89/1.50  --sup_prop_simpl_given                  true
% 7.89/1.50  --sup_fun_splitting                     false
% 7.89/1.50  --sup_smt_interval                      50000
% 7.89/1.50  
% 7.89/1.50  ------ Superposition Simplification Setup
% 7.89/1.50  
% 7.89/1.50  --sup_indices_passive                   []
% 7.89/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.50  --sup_full_bw                           [BwDemod]
% 7.89/1.50  --sup_immed_triv                        [TrivRules]
% 7.89/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.50  --sup_immed_bw_main                     []
% 7.89/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.89/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.89/1.50  
% 7.89/1.50  ------ Combination Options
% 7.89/1.50  
% 7.89/1.50  --comb_res_mult                         3
% 7.89/1.50  --comb_sup_mult                         2
% 7.89/1.50  --comb_inst_mult                        10
% 7.89/1.50  
% 7.89/1.50  ------ Debug Options
% 7.89/1.50  
% 7.89/1.50  --dbg_backtrace                         false
% 7.89/1.50  --dbg_dump_prop_clauses                 false
% 7.89/1.50  --dbg_dump_prop_clauses_file            -
% 7.89/1.50  --dbg_out_stat                          false
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  ------ Proving...
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  % SZS status Theorem for theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  fof(f4,axiom,(
% 7.89/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f13,plain,(
% 7.89/1.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.89/1.50    inference(ennf_transformation,[],[f4])).
% 7.89/1.50  
% 7.89/1.50  fof(f25,plain,(
% 7.89/1.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.89/1.50    inference(cnf_transformation,[],[f13])).
% 7.89/1.50  
% 7.89/1.50  fof(f8,conjecture,(
% 7.89/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 7.89/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.50  
% 7.89/1.50  fof(f9,negated_conjecture,(
% 7.89/1.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 7.89/1.50    inference(negated_conjecture,[],[f8])).
% 7.89/1.50  
% 7.89/1.50  fof(f18,plain,(
% 7.89/1.50    ? [X0] : (? [X1] : (k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.89/1.50    inference(ennf_transformation,[],[f9])).
% 7.89/1.50  
% 7.89/1.50  fof(f20,plain,(
% 7.89/1.50    ( ! [X0] : (? [X1] : (k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1)) & v1_relat_1(X1)) => (k10_relat_1(X0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(X0,sK1)) & v1_relat_1(sK1))) )),
% 7.89/1.50    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f19,plain,(
% 7.89/1.51    ? [X0] : (? [X1] : (k10_relat_1(X0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k10_relat_1(sK0,k1_relat_1(X1)) != k1_relat_1(k5_relat_1(sK0,X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f21,plain,(
% 7.89/1.51    (k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 7.89/1.51  
% 7.89/1.51  fof(f30,plain,(
% 7.89/1.51    v1_relat_1(sK1)),
% 7.89/1.51    inference(cnf_transformation,[],[f21])).
% 7.89/1.51  
% 7.89/1.51  fof(f29,plain,(
% 7.89/1.51    v1_relat_1(sK0)),
% 7.89/1.51    inference(cnf_transformation,[],[f21])).
% 7.89/1.51  
% 7.89/1.51  fof(f3,axiom,(
% 7.89/1.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f11,plain,(
% 7.89/1.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.89/1.51    inference(ennf_transformation,[],[f3])).
% 7.89/1.51  
% 7.89/1.51  fof(f12,plain,(
% 7.89/1.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(flattening,[],[f11])).
% 7.89/1.51  
% 7.89/1.51  fof(f24,plain,(
% 7.89/1.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f12])).
% 7.89/1.51  
% 7.89/1.51  fof(f5,axiom,(
% 7.89/1.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f14,plain,(
% 7.89/1.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(ennf_transformation,[],[f5])).
% 7.89/1.51  
% 7.89/1.51  fof(f26,plain,(
% 7.89/1.51    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f14])).
% 7.89/1.51  
% 7.89/1.51  fof(f7,axiom,(
% 7.89/1.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f17,plain,(
% 7.89/1.51    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 7.89/1.51    inference(ennf_transformation,[],[f7])).
% 7.89/1.51  
% 7.89/1.51  fof(f28,plain,(
% 7.89/1.51    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f17])).
% 7.89/1.51  
% 7.89/1.51  fof(f6,axiom,(
% 7.89/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f15,plain,(
% 7.89/1.51    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.89/1.51    inference(ennf_transformation,[],[f6])).
% 7.89/1.51  
% 7.89/1.51  fof(f16,plain,(
% 7.89/1.51    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.89/1.51    inference(flattening,[],[f15])).
% 7.89/1.51  
% 7.89/1.51  fof(f27,plain,(
% 7.89/1.51    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f16])).
% 7.89/1.51  
% 7.89/1.51  fof(f2,axiom,(
% 7.89/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f10,plain,(
% 7.89/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.89/1.51    inference(ennf_transformation,[],[f2])).
% 7.89/1.51  
% 7.89/1.51  fof(f23,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f10])).
% 7.89/1.51  
% 7.89/1.51  fof(f1,axiom,(
% 7.89/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.89/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f22,plain,(
% 7.89/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f1])).
% 7.89/1.51  
% 7.89/1.51  fof(f31,plain,(
% 7.89/1.51    k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))),
% 7.89/1.51    inference(cnf_transformation,[],[f21])).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f25]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_88,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(X0_37,X0_38),k1_relat_1(X0_37))
% 7.89/1.51      | ~ v1_relat_1(X0_37) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_236,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(X0_37,X0_38),k1_relat_1(X0_37)) = iProver_top
% 7.89/1.51      | v1_relat_1(X0_37) != iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_88]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_8,negated_conjecture,
% 7.89/1.51      ( v1_relat_1(sK1) ),
% 7.89/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_83,negated_conjecture,
% 7.89/1.51      ( v1_relat_1(sK1) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_240,plain,
% 7.89/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_83]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_9,negated_conjecture,
% 7.89/1.51      ( v1_relat_1(sK0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_82,negated_conjecture,
% 7.89/1.51      ( v1_relat_1(sK0) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_9]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_241,plain,
% 7.89/1.51      ( v1_relat_1(sK0) = iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_82]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2,plain,
% 7.89/1.51      ( ~ v1_relat_1(X0)
% 7.89/1.51      | ~ v1_relat_1(X1)
% 7.89/1.51      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 7.89/1.51      inference(cnf_transformation,[],[f24]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_89,plain,
% 7.89/1.51      ( ~ v1_relat_1(X0_37)
% 7.89/1.51      | ~ v1_relat_1(X1_37)
% 7.89/1.51      | v1_relat_1(k5_relat_1(X1_37,X0_37)) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_235,plain,
% 7.89/1.51      ( v1_relat_1(X0_37) != iProver_top
% 7.89/1.51      | v1_relat_1(X1_37) != iProver_top
% 7.89/1.51      | v1_relat_1(k5_relat_1(X1_37,X0_37)) = iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_89]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4,plain,
% 7.89/1.51      ( ~ v1_relat_1(X0)
% 7.89/1.51      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_87,plain,
% 7.89/1.51      ( ~ v1_relat_1(X0_37)
% 7.89/1.51      | k10_relat_1(X0_37,k2_relat_1(X0_37)) = k1_relat_1(X0_37) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_4]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_237,plain,
% 7.89/1.51      ( k10_relat_1(X0_37,k2_relat_1(X0_37)) = k1_relat_1(X0_37)
% 7.89/1.51      | v1_relat_1(X0_37) != iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_87]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_590,plain,
% 7.89/1.51      ( k10_relat_1(k5_relat_1(X0_37,X1_37),k2_relat_1(k5_relat_1(X0_37,X1_37))) = k1_relat_1(k5_relat_1(X0_37,X1_37))
% 7.89/1.51      | v1_relat_1(X1_37) != iProver_top
% 7.89/1.51      | v1_relat_1(X0_37) != iProver_top ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_235,c_237]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1352,plain,
% 7.89/1.51      ( k10_relat_1(k5_relat_1(sK0,X0_37),k2_relat_1(k5_relat_1(sK0,X0_37))) = k1_relat_1(k5_relat_1(sK0,X0_37))
% 7.89/1.51      | v1_relat_1(X0_37) != iProver_top ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_241,c_590]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3569,plain,
% 7.89/1.51      ( k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_240,c_1352]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6,plain,
% 7.89/1.51      ( ~ v1_relat_1(X0)
% 7.89/1.51      | ~ v1_relat_1(X1)
% 7.89/1.51      | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
% 7.89/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_85,plain,
% 7.89/1.51      ( ~ v1_relat_1(X0_37)
% 7.89/1.51      | ~ v1_relat_1(X1_37)
% 7.89/1.51      | k10_relat_1(k5_relat_1(X0_37,X1_37),X0_38) = k10_relat_1(X0_37,k10_relat_1(X1_37,X0_38)) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_6]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_239,plain,
% 7.89/1.51      ( k10_relat_1(k5_relat_1(X0_37,X1_37),X0_38) = k10_relat_1(X0_37,k10_relat_1(X1_37,X0_38))
% 7.89/1.51      | v1_relat_1(X0_37) != iProver_top
% 7.89/1.51      | v1_relat_1(X1_37) != iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_85]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_719,plain,
% 7.89/1.51      ( k10_relat_1(sK0,k10_relat_1(X0_37,X0_38)) = k10_relat_1(k5_relat_1(sK0,X0_37),X0_38)
% 7.89/1.51      | v1_relat_1(X0_37) != iProver_top ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_241,c_239]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2623,plain,
% 7.89/1.51      ( k10_relat_1(sK0,k10_relat_1(sK1,X0_38)) = k10_relat_1(k5_relat_1(sK0,sK1),X0_38) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_240,c_719]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3944,plain,
% 7.89/1.51      ( k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_3569,c_2623]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_5,plain,
% 7.89/1.51      ( ~ r1_tarski(X0,X1)
% 7.89/1.51      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
% 7.89/1.51      | ~ v1_relat_1(X2) ),
% 7.89/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_86,plain,
% 7.89/1.51      ( ~ r1_tarski(X0_38,X1_38)
% 7.89/1.51      | r1_tarski(k10_relat_1(X0_37,X0_38),k10_relat_1(X0_37,X1_38))
% 7.89/1.51      | ~ v1_relat_1(X0_37) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_5]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_238,plain,
% 7.89/1.51      ( r1_tarski(X0_38,X1_38) != iProver_top
% 7.89/1.51      | r1_tarski(k10_relat_1(X0_37,X0_38),k10_relat_1(X0_37,X1_38)) = iProver_top
% 7.89/1.51      | v1_relat_1(X0_37) != iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_86]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_24518,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X0_38) != iProver_top
% 7.89/1.51      | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X0_38)) = iProver_top
% 7.89/1.51      | v1_relat_1(sK0) != iProver_top ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_3944,c_238]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_10,plain,
% 7.89/1.51      ( v1_relat_1(sK0) = iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_29013,plain,
% 7.89/1.51      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X0_38)) = iProver_top
% 7.89/1.51      | r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X0_38) != iProver_top ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_24518,c_10]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_29014,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X0_38) != iProver_top
% 7.89/1.51      | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X0_38)) = iProver_top ),
% 7.89/1.51      inference(renaming,[status(thm)],[c_29013]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_29022,plain,
% 7.89/1.51      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 7.89/1.51      | v1_relat_1(sK1) != iProver_top ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_236,c_29014]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_588,plain,
% 7.89/1.51      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_240,c_237]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2807,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0_38)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 7.89/1.51      | v1_relat_1(k5_relat_1(sK0,sK1)) != iProver_top ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_2623,c_236]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_11,plain,
% 7.89/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_659,plain,
% 7.89/1.51      ( v1_relat_1(k5_relat_1(sK0,sK1))
% 7.89/1.51      | ~ v1_relat_1(sK1)
% 7.89/1.51      | ~ v1_relat_1(sK0) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_89]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_660,plain,
% 7.89/1.51      ( v1_relat_1(k5_relat_1(sK0,sK1)) = iProver_top
% 7.89/1.51      | v1_relat_1(sK1) != iProver_top
% 7.89/1.51      | v1_relat_1(sK0) != iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6449,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0_38)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_2807,c_10,c_11,c_660]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6456,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 7.89/1.51      inference(superposition,[status(thm)],[c_588,c_6449]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_94,plain,
% 7.89/1.51      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 7.89/1.51      theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_93,plain,( X0_38 = X0_38 ),theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_626,plain,
% 7.89/1.51      ( X0_38 != X1_38 | X1_38 = X0_38 ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_94,c_93]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1,plain,
% 7.89/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.89/1.51      inference(cnf_transformation,[],[f23]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_90,plain,
% 7.89/1.51      ( ~ r1_tarski(X0_38,X1_38) | k3_xboole_0(X0_38,X1_38) = X0_38 ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_1]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_637,plain,
% 7.89/1.51      ( ~ r1_tarski(X0_38,X1_38) | X0_38 = k3_xboole_0(X0_38,X1_38) ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_626,c_90]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_651,plain,
% 7.89/1.51      ( ~ r1_tarski(X0_38,X1_38)
% 7.89/1.51      | X0_38 = X2_38
% 7.89/1.51      | X2_38 != k3_xboole_0(X0_38,X1_38) ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_637,c_94]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_0,plain,
% 7.89/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f22]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_91,plain,
% 7.89/1.51      ( k3_xboole_0(X0_38,X1_38) = k3_xboole_0(X1_38,X0_38) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_0]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_624,plain,
% 7.89/1.51      ( X0_38 != k3_xboole_0(X1_38,X2_38)
% 7.89/1.51      | k3_xboole_0(X2_38,X1_38) = X0_38 ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_94,c_91]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1185,plain,
% 7.89/1.51      ( ~ r1_tarski(X0_38,X1_38) | k3_xboole_0(X1_38,X0_38) = X0_38 ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_624,c_637]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1193,plain,
% 7.89/1.51      ( ~ r1_tarski(X0_38,X1_38) | X0_38 = k3_xboole_0(X1_38,X0_38) ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_1185,c_626]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1754,plain,
% 7.89/1.51      ( ~ r1_tarski(X0_38,X1_38)
% 7.89/1.51      | ~ r1_tarski(X1_38,X0_38)
% 7.89/1.51      | X0_38 = X1_38 ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_651,c_1193]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7,negated_conjecture,
% 7.89/1.51      ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.89/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_84,negated_conjecture,
% 7.89/1.51      ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.89/1.51      inference(subtyping,[status(esa)],[c_7]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2013,plain,
% 7.89/1.51      ( ~ r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.89/1.51      | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
% 7.89/1.51      inference(resolution,[status(thm)],[c_1754,c_84]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2014,plain,
% 7.89/1.51      ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 7.89/1.51      | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) != iProver_top ),
% 7.89/1.51      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(contradiction,plain,
% 7.89/1.51      ( $false ),
% 7.89/1.51      inference(minisat,[status(thm)],[c_29022,c_6456,c_2014,c_11]) ).
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  ------                               Statistics
% 7.89/1.51  
% 7.89/1.51  ------ Selected
% 7.89/1.51  
% 7.89/1.51  total_time:                             0.891
% 7.89/1.51  
%------------------------------------------------------------------------------
