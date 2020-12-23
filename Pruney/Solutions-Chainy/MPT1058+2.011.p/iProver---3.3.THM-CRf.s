%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:13 EST 2020

% Result     : Theorem 55.34s
% Output     : CNFRefutation 55.34s
% Verified   : 
% Statistics : Number of formulae       :  145 (3677 expanded)
%              Number of clauses        :   86 (1520 expanded)
%              Number of leaves         :   19 ( 914 expanded)
%              Depth                    :   24
%              Number of atoms          :  277 (4718 expanded)
%              Number of equality atoms :  171 (3438 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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

fof(f33,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32,f31])).

fof(f56,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f37,f37])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_494,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_704,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_1108,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_704,c_8])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_788,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_1496,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_788,c_0])).

cnf(c_1618,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1108,c_1496])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_503,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1354,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_503])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_502,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1610,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1354,c_502])).

cnf(c_1370,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1354])).

cnf(c_3740,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1370,c_502])).

cnf(c_1230,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1108,c_5])).

cnf(c_4174,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1610,c_1230])).

cnf(c_5444,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1618,c_1610,c_3740,c_4174])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_498,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_497,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1711,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(superposition,[status(thm)],[c_498,c_497])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_500,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1843,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_498,c_500])).

cnf(c_18,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1848,plain,
    ( k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1843,c_18])).

cnf(c_4939,plain,
    ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(light_normalisation,[status(thm)],[c_1711,c_1848])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_504,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_495,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1118,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_504,c_495])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_505,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2647,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_505])).

cnf(c_7321,plain,
    ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),k9_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)) = X2
    | r1_tarski(X2,k1_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2))),X2) != iProver_top
    | v1_funct_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top
    | v1_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4939,c_2647])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_501,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1964,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_498,c_501])).

cnf(c_1969,plain,
    ( k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1964,c_1848])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1970,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1969,c_10])).

cnf(c_4944,plain,
    ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(superposition,[status(thm)],[c_1108,c_4939])).

cnf(c_7334,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) = X2
    | r1_tarski(X2,k3_xboole_0(X0,X1)) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),k3_xboole_0(k3_xboole_0(X0,X1),X2))),X2) != iProver_top
    | v1_funct_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top
    | v1_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7321,c_11,c_1970,c_4944])).

cnf(c_13,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_499,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7558,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) = X2
    | r1_tarski(X2,k3_xboole_0(X0,X1)) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),k3_xboole_0(k3_xboole_0(X0,X1),X2))),X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7334,c_498,c_499])).

cnf(c_7579,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))) = X1
    | r1_tarski(X1,k3_xboole_0(X0,X0)) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5444,c_7558])).

cnf(c_7615,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7579,c_5444])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_496,plain,
    ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1475,plain,
    ( k3_xboole_0(X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_496])).

cnf(c_1483,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1475,c_11])).

cnf(c_36,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3339,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1483,c_36])).

cnf(c_3342,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_3339,c_1970])).

cnf(c_3348,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_3342,c_1970])).

cnf(c_6188,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3348,c_5444])).

cnf(c_7616,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X0),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7615,c_6188])).

cnf(c_6202,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_6188,c_0])).

cnf(c_6214,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_6202,c_6188])).

cnf(c_6805,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1108,c_6214])).

cnf(c_7008,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[status(thm)],[c_6188,c_6805])).

cnf(c_7022,plain,
    ( k3_xboole_0(k10_relat_1(k6_relat_1(X0),X1),X0) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_7008,c_6214])).

cnf(c_5474,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_5444,c_4939])).

cnf(c_75099,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5474,c_6188])).

cnf(c_163395,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7022,c_75099])).

cnf(c_163416,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1108,c_163395])).

cnf(c_208701,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7616,c_163416])).

cnf(c_208702,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_208701,c_163416])).

cnf(c_208706,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_208702,c_1354])).

cnf(c_208710,plain,
    ( k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_494,c_208706])).

cnf(c_209076,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_208710,c_1108])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_492,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1712,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_492,c_497])).

cnf(c_19,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5590,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) != k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1712,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_209076,c_5590])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:50:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 55.34/7.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.34/7.49  
% 55.34/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.34/7.49  
% 55.34/7.49  ------  iProver source info
% 55.34/7.49  
% 55.34/7.49  git: date: 2020-06-30 10:37:57 +0100
% 55.34/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.34/7.49  git: non_committed_changes: false
% 55.34/7.49  git: last_make_outside_of_git: false
% 55.34/7.49  
% 55.34/7.49  ------ 
% 55.34/7.49  
% 55.34/7.49  ------ Input Options
% 55.34/7.49  
% 55.34/7.49  --out_options                           all
% 55.34/7.49  --tptp_safe_out                         true
% 55.34/7.49  --problem_path                          ""
% 55.34/7.49  --include_path                          ""
% 55.34/7.49  --clausifier                            res/vclausify_rel
% 55.34/7.49  --clausifier_options                    --mode clausify
% 55.34/7.49  --stdin                                 false
% 55.34/7.49  --stats_out                             sel
% 55.34/7.49  
% 55.34/7.49  ------ General Options
% 55.34/7.49  
% 55.34/7.49  --fof                                   false
% 55.34/7.49  --time_out_real                         604.99
% 55.34/7.49  --time_out_virtual                      -1.
% 55.34/7.49  --symbol_type_check                     false
% 55.34/7.49  --clausify_out                          false
% 55.34/7.49  --sig_cnt_out                           false
% 55.34/7.49  --trig_cnt_out                          false
% 55.34/7.49  --trig_cnt_out_tolerance                1.
% 55.34/7.49  --trig_cnt_out_sk_spl                   false
% 55.34/7.49  --abstr_cl_out                          false
% 55.34/7.49  
% 55.34/7.49  ------ Global Options
% 55.34/7.49  
% 55.34/7.49  --schedule                              none
% 55.34/7.49  --add_important_lit                     false
% 55.34/7.49  --prop_solver_per_cl                    1000
% 55.34/7.49  --min_unsat_core                        false
% 55.34/7.49  --soft_assumptions                      false
% 55.34/7.49  --soft_lemma_size                       3
% 55.34/7.49  --prop_impl_unit_size                   0
% 55.34/7.49  --prop_impl_unit                        []
% 55.34/7.49  --share_sel_clauses                     true
% 55.34/7.49  --reset_solvers                         false
% 55.34/7.49  --bc_imp_inh                            [conj_cone]
% 55.34/7.49  --conj_cone_tolerance                   3.
% 55.34/7.49  --extra_neg_conj                        none
% 55.34/7.49  --large_theory_mode                     true
% 55.34/7.49  --prolific_symb_bound                   200
% 55.34/7.49  --lt_threshold                          2000
% 55.34/7.49  --clause_weak_htbl                      true
% 55.34/7.49  --gc_record_bc_elim                     false
% 55.34/7.49  
% 55.34/7.49  ------ Preprocessing Options
% 55.34/7.49  
% 55.34/7.49  --preprocessing_flag                    true
% 55.34/7.49  --time_out_prep_mult                    0.1
% 55.34/7.49  --splitting_mode                        input
% 55.34/7.49  --splitting_grd                         true
% 55.34/7.49  --splitting_cvd                         false
% 55.34/7.49  --splitting_cvd_svl                     false
% 55.34/7.49  --splitting_nvd                         32
% 55.34/7.49  --sub_typing                            true
% 55.34/7.49  --prep_gs_sim                           false
% 55.34/7.49  --prep_unflatten                        true
% 55.34/7.49  --prep_res_sim                          true
% 55.34/7.49  --prep_upred                            true
% 55.34/7.49  --prep_sem_filter                       exhaustive
% 55.34/7.49  --prep_sem_filter_out                   false
% 55.34/7.49  --pred_elim                             false
% 55.34/7.49  --res_sim_input                         true
% 55.34/7.49  --eq_ax_congr_red                       true
% 55.34/7.49  --pure_diseq_elim                       true
% 55.34/7.49  --brand_transform                       false
% 55.34/7.49  --non_eq_to_eq                          false
% 55.34/7.49  --prep_def_merge                        true
% 55.34/7.49  --prep_def_merge_prop_impl              false
% 55.34/7.49  --prep_def_merge_mbd                    true
% 55.34/7.49  --prep_def_merge_tr_red                 false
% 55.34/7.49  --prep_def_merge_tr_cl                  false
% 55.34/7.49  --smt_preprocessing                     true
% 55.34/7.49  --smt_ac_axioms                         fast
% 55.34/7.49  --preprocessed_out                      false
% 55.34/7.49  --preprocessed_stats                    false
% 55.34/7.49  
% 55.34/7.49  ------ Abstraction refinement Options
% 55.34/7.49  
% 55.34/7.49  --abstr_ref                             []
% 55.34/7.49  --abstr_ref_prep                        false
% 55.34/7.49  --abstr_ref_until_sat                   false
% 55.34/7.49  --abstr_ref_sig_restrict                funpre
% 55.34/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.34/7.49  --abstr_ref_under                       []
% 55.34/7.49  
% 55.34/7.49  ------ SAT Options
% 55.34/7.49  
% 55.34/7.49  --sat_mode                              false
% 55.34/7.49  --sat_fm_restart_options                ""
% 55.34/7.49  --sat_gr_def                            false
% 55.34/7.49  --sat_epr_types                         true
% 55.34/7.49  --sat_non_cyclic_types                  false
% 55.34/7.49  --sat_finite_models                     false
% 55.34/7.49  --sat_fm_lemmas                         false
% 55.34/7.49  --sat_fm_prep                           false
% 55.34/7.49  --sat_fm_uc_incr                        true
% 55.34/7.49  --sat_out_model                         small
% 55.34/7.49  --sat_out_clauses                       false
% 55.34/7.49  
% 55.34/7.49  ------ QBF Options
% 55.34/7.49  
% 55.34/7.49  --qbf_mode                              false
% 55.34/7.49  --qbf_elim_univ                         false
% 55.34/7.49  --qbf_dom_inst                          none
% 55.34/7.49  --qbf_dom_pre_inst                      false
% 55.34/7.49  --qbf_sk_in                             false
% 55.34/7.49  --qbf_pred_elim                         true
% 55.34/7.49  --qbf_split                             512
% 55.34/7.49  
% 55.34/7.49  ------ BMC1 Options
% 55.34/7.49  
% 55.34/7.49  --bmc1_incremental                      false
% 55.34/7.49  --bmc1_axioms                           reachable_all
% 55.34/7.49  --bmc1_min_bound                        0
% 55.34/7.49  --bmc1_max_bound                        -1
% 55.34/7.49  --bmc1_max_bound_default                -1
% 55.34/7.49  --bmc1_symbol_reachability              true
% 55.34/7.49  --bmc1_property_lemmas                  false
% 55.34/7.49  --bmc1_k_induction                      false
% 55.34/7.49  --bmc1_non_equiv_states                 false
% 55.34/7.49  --bmc1_deadlock                         false
% 55.34/7.49  --bmc1_ucm                              false
% 55.34/7.49  --bmc1_add_unsat_core                   none
% 55.34/7.49  --bmc1_unsat_core_children              false
% 55.34/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.34/7.49  --bmc1_out_stat                         full
% 55.34/7.49  --bmc1_ground_init                      false
% 55.34/7.49  --bmc1_pre_inst_next_state              false
% 55.34/7.49  --bmc1_pre_inst_state                   false
% 55.34/7.49  --bmc1_pre_inst_reach_state             false
% 55.34/7.49  --bmc1_out_unsat_core                   false
% 55.34/7.49  --bmc1_aig_witness_out                  false
% 55.34/7.49  --bmc1_verbose                          false
% 55.34/7.49  --bmc1_dump_clauses_tptp                false
% 55.34/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.34/7.49  --bmc1_dump_file                        -
% 55.34/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.34/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.34/7.49  --bmc1_ucm_extend_mode                  1
% 55.34/7.49  --bmc1_ucm_init_mode                    2
% 55.34/7.49  --bmc1_ucm_cone_mode                    none
% 55.34/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.34/7.49  --bmc1_ucm_relax_model                  4
% 55.34/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.34/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.34/7.49  --bmc1_ucm_layered_model                none
% 55.34/7.49  --bmc1_ucm_max_lemma_size               10
% 55.34/7.49  
% 55.34/7.49  ------ AIG Options
% 55.34/7.49  
% 55.34/7.49  --aig_mode                              false
% 55.34/7.49  
% 55.34/7.49  ------ Instantiation Options
% 55.34/7.49  
% 55.34/7.49  --instantiation_flag                    true
% 55.34/7.49  --inst_sos_flag                         false
% 55.34/7.49  --inst_sos_phase                        true
% 55.34/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.34/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.34/7.49  --inst_lit_sel_side                     num_symb
% 55.34/7.49  --inst_solver_per_active                1400
% 55.34/7.49  --inst_solver_calls_frac                1.
% 55.34/7.49  --inst_passive_queue_type               priority_queues
% 55.34/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.34/7.49  --inst_passive_queues_freq              [25;2]
% 55.34/7.49  --inst_dismatching                      true
% 55.34/7.49  --inst_eager_unprocessed_to_passive     true
% 55.34/7.49  --inst_prop_sim_given                   true
% 55.34/7.49  --inst_prop_sim_new                     false
% 55.34/7.49  --inst_subs_new                         false
% 55.34/7.49  --inst_eq_res_simp                      false
% 55.34/7.49  --inst_subs_given                       false
% 55.34/7.49  --inst_orphan_elimination               true
% 55.34/7.49  --inst_learning_loop_flag               true
% 55.34/7.49  --inst_learning_start                   3000
% 55.34/7.49  --inst_learning_factor                  2
% 55.34/7.49  --inst_start_prop_sim_after_learn       3
% 55.34/7.49  --inst_sel_renew                        solver
% 55.34/7.49  --inst_lit_activity_flag                true
% 55.34/7.49  --inst_restr_to_given                   false
% 55.34/7.49  --inst_activity_threshold               500
% 55.34/7.49  --inst_out_proof                        true
% 55.34/7.49  
% 55.34/7.49  ------ Resolution Options
% 55.34/7.49  
% 55.34/7.49  --resolution_flag                       true
% 55.34/7.49  --res_lit_sel                           adaptive
% 55.34/7.49  --res_lit_sel_side                      none
% 55.34/7.49  --res_ordering                          kbo
% 55.34/7.49  --res_to_prop_solver                    active
% 55.34/7.49  --res_prop_simpl_new                    false
% 55.34/7.49  --res_prop_simpl_given                  true
% 55.34/7.49  --res_passive_queue_type                priority_queues
% 55.34/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.34/7.49  --res_passive_queues_freq               [15;5]
% 55.34/7.49  --res_forward_subs                      full
% 55.34/7.49  --res_backward_subs                     full
% 55.34/7.49  --res_forward_subs_resolution           true
% 55.34/7.49  --res_backward_subs_resolution          true
% 55.34/7.49  --res_orphan_elimination                true
% 55.34/7.49  --res_time_limit                        2.
% 55.34/7.49  --res_out_proof                         true
% 55.34/7.49  
% 55.34/7.49  ------ Superposition Options
% 55.34/7.49  
% 55.34/7.49  --superposition_flag                    true
% 55.34/7.49  --sup_passive_queue_type                priority_queues
% 55.34/7.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.34/7.49  --sup_passive_queues_freq               [1;4]
% 55.34/7.49  --demod_completeness_check              fast
% 55.34/7.49  --demod_use_ground                      true
% 55.34/7.49  --sup_to_prop_solver                    passive
% 55.34/7.49  --sup_prop_simpl_new                    true
% 55.34/7.49  --sup_prop_simpl_given                  true
% 55.34/7.49  --sup_fun_splitting                     false
% 55.34/7.49  --sup_smt_interval                      50000
% 55.34/7.49  
% 55.34/7.49  ------ Superposition Simplification Setup
% 55.34/7.49  
% 55.34/7.49  --sup_indices_passive                   []
% 55.34/7.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.34/7.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.34/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.34/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 55.34/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.34/7.49  --sup_full_bw                           [BwDemod]
% 55.34/7.49  --sup_immed_triv                        [TrivRules]
% 55.34/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.34/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.34/7.49  --sup_immed_bw_main                     []
% 55.34/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.34/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.34/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.34/7.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.34/7.49  
% 55.34/7.49  ------ Combination Options
% 55.34/7.49  
% 55.34/7.49  --comb_res_mult                         3
% 55.34/7.49  --comb_sup_mult                         2
% 55.34/7.49  --comb_inst_mult                        10
% 55.34/7.49  
% 55.34/7.49  ------ Debug Options
% 55.34/7.49  
% 55.34/7.49  --dbg_backtrace                         false
% 55.34/7.49  --dbg_dump_prop_clauses                 false
% 55.34/7.49  --dbg_dump_prop_clauses_file            -
% 55.34/7.49  --dbg_out_stat                          false
% 55.34/7.49  ------ Parsing...
% 55.34/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.34/7.49  
% 55.34/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 55.34/7.49  
% 55.34/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.34/7.49  
% 55.34/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.34/7.49  ------ Proving...
% 55.34/7.49  ------ Problem Properties 
% 55.34/7.49  
% 55.34/7.49  
% 55.34/7.49  clauses                                 22
% 55.34/7.49  conjectures                             4
% 55.34/7.49  EPR                                     5
% 55.34/7.49  Horn                                    22
% 55.34/7.49  unary                                   15
% 55.34/7.49  binary                                  4
% 55.34/7.49  lits                                    34
% 55.34/7.49  lits eq                                 14
% 55.34/7.49  fd_pure                                 0
% 55.34/7.49  fd_pseudo                               0
% 55.34/7.49  fd_cond                                 1
% 55.34/7.49  fd_pseudo_cond                          1
% 55.34/7.49  AC symbols                              0
% 55.34/7.49  
% 55.34/7.49  ------ Input Options Time Limit: Unbounded
% 55.34/7.49  
% 55.34/7.49  
% 55.34/7.49  ------ 
% 55.34/7.49  Current options:
% 55.34/7.49  ------ 
% 55.34/7.49  
% 55.34/7.49  ------ Input Options
% 55.34/7.49  
% 55.34/7.49  --out_options                           all
% 55.34/7.49  --tptp_safe_out                         true
% 55.34/7.49  --problem_path                          ""
% 55.34/7.49  --include_path                          ""
% 55.34/7.49  --clausifier                            res/vclausify_rel
% 55.34/7.49  --clausifier_options                    --mode clausify
% 55.34/7.49  --stdin                                 false
% 55.34/7.49  --stats_out                             sel
% 55.34/7.49  
% 55.34/7.49  ------ General Options
% 55.34/7.49  
% 55.34/7.49  --fof                                   false
% 55.34/7.49  --time_out_real                         604.99
% 55.34/7.49  --time_out_virtual                      -1.
% 55.34/7.49  --symbol_type_check                     false
% 55.34/7.49  --clausify_out                          false
% 55.34/7.49  --sig_cnt_out                           false
% 55.34/7.49  --trig_cnt_out                          false
% 55.34/7.49  --trig_cnt_out_tolerance                1.
% 55.34/7.49  --trig_cnt_out_sk_spl                   false
% 55.34/7.49  --abstr_cl_out                          false
% 55.34/7.49  
% 55.34/7.49  ------ Global Options
% 55.34/7.49  
% 55.34/7.49  --schedule                              none
% 55.34/7.49  --add_important_lit                     false
% 55.34/7.49  --prop_solver_per_cl                    1000
% 55.34/7.49  --min_unsat_core                        false
% 55.34/7.49  --soft_assumptions                      false
% 55.34/7.49  --soft_lemma_size                       3
% 55.34/7.49  --prop_impl_unit_size                   0
% 55.34/7.49  --prop_impl_unit                        []
% 55.34/7.49  --share_sel_clauses                     true
% 55.34/7.49  --reset_solvers                         false
% 55.34/7.49  --bc_imp_inh                            [conj_cone]
% 55.34/7.49  --conj_cone_tolerance                   3.
% 55.34/7.49  --extra_neg_conj                        none
% 55.34/7.49  --large_theory_mode                     true
% 55.34/7.49  --prolific_symb_bound                   200
% 55.34/7.49  --lt_threshold                          2000
% 55.34/7.49  --clause_weak_htbl                      true
% 55.34/7.49  --gc_record_bc_elim                     false
% 55.34/7.49  
% 55.34/7.49  ------ Preprocessing Options
% 55.34/7.49  
% 55.34/7.49  --preprocessing_flag                    true
% 55.34/7.49  --time_out_prep_mult                    0.1
% 55.34/7.49  --splitting_mode                        input
% 55.34/7.49  --splitting_grd                         true
% 55.34/7.49  --splitting_cvd                         false
% 55.34/7.49  --splitting_cvd_svl                     false
% 55.34/7.49  --splitting_nvd                         32
% 55.34/7.49  --sub_typing                            true
% 55.34/7.49  --prep_gs_sim                           false
% 55.34/7.49  --prep_unflatten                        true
% 55.34/7.49  --prep_res_sim                          true
% 55.34/7.49  --prep_upred                            true
% 55.34/7.49  --prep_sem_filter                       exhaustive
% 55.34/7.49  --prep_sem_filter_out                   false
% 55.34/7.49  --pred_elim                             false
% 55.34/7.49  --res_sim_input                         true
% 55.34/7.49  --eq_ax_congr_red                       true
% 55.34/7.49  --pure_diseq_elim                       true
% 55.34/7.49  --brand_transform                       false
% 55.34/7.49  --non_eq_to_eq                          false
% 55.34/7.49  --prep_def_merge                        true
% 55.34/7.49  --prep_def_merge_prop_impl              false
% 55.34/7.49  --prep_def_merge_mbd                    true
% 55.34/7.49  --prep_def_merge_tr_red                 false
% 55.34/7.49  --prep_def_merge_tr_cl                  false
% 55.34/7.49  --smt_preprocessing                     true
% 55.34/7.49  --smt_ac_axioms                         fast
% 55.34/7.49  --preprocessed_out                      false
% 55.34/7.49  --preprocessed_stats                    false
% 55.34/7.49  
% 55.34/7.49  ------ Abstraction refinement Options
% 55.34/7.49  
% 55.34/7.49  --abstr_ref                             []
% 55.34/7.49  --abstr_ref_prep                        false
% 55.34/7.49  --abstr_ref_until_sat                   false
% 55.34/7.49  --abstr_ref_sig_restrict                funpre
% 55.34/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.34/7.49  --abstr_ref_under                       []
% 55.34/7.49  
% 55.34/7.49  ------ SAT Options
% 55.34/7.49  
% 55.34/7.49  --sat_mode                              false
% 55.34/7.49  --sat_fm_restart_options                ""
% 55.34/7.49  --sat_gr_def                            false
% 55.34/7.49  --sat_epr_types                         true
% 55.34/7.49  --sat_non_cyclic_types                  false
% 55.34/7.49  --sat_finite_models                     false
% 55.34/7.49  --sat_fm_lemmas                         false
% 55.34/7.49  --sat_fm_prep                           false
% 55.34/7.49  --sat_fm_uc_incr                        true
% 55.34/7.49  --sat_out_model                         small
% 55.34/7.49  --sat_out_clauses                       false
% 55.34/7.49  
% 55.34/7.49  ------ QBF Options
% 55.34/7.49  
% 55.34/7.49  --qbf_mode                              false
% 55.34/7.49  --qbf_elim_univ                         false
% 55.34/7.49  --qbf_dom_inst                          none
% 55.34/7.49  --qbf_dom_pre_inst                      false
% 55.34/7.49  --qbf_sk_in                             false
% 55.34/7.49  --qbf_pred_elim                         true
% 55.34/7.49  --qbf_split                             512
% 55.34/7.49  
% 55.34/7.49  ------ BMC1 Options
% 55.34/7.49  
% 55.34/7.49  --bmc1_incremental                      false
% 55.34/7.49  --bmc1_axioms                           reachable_all
% 55.34/7.49  --bmc1_min_bound                        0
% 55.34/7.49  --bmc1_max_bound                        -1
% 55.34/7.49  --bmc1_max_bound_default                -1
% 55.34/7.49  --bmc1_symbol_reachability              true
% 55.34/7.49  --bmc1_property_lemmas                  false
% 55.34/7.49  --bmc1_k_induction                      false
% 55.34/7.49  --bmc1_non_equiv_states                 false
% 55.34/7.49  --bmc1_deadlock                         false
% 55.34/7.49  --bmc1_ucm                              false
% 55.34/7.49  --bmc1_add_unsat_core                   none
% 55.34/7.49  --bmc1_unsat_core_children              false
% 55.34/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.34/7.49  --bmc1_out_stat                         full
% 55.34/7.49  --bmc1_ground_init                      false
% 55.34/7.49  --bmc1_pre_inst_next_state              false
% 55.34/7.49  --bmc1_pre_inst_state                   false
% 55.34/7.49  --bmc1_pre_inst_reach_state             false
% 55.34/7.49  --bmc1_out_unsat_core                   false
% 55.34/7.49  --bmc1_aig_witness_out                  false
% 55.34/7.49  --bmc1_verbose                          false
% 55.34/7.49  --bmc1_dump_clauses_tptp                false
% 55.34/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.34/7.49  --bmc1_dump_file                        -
% 55.34/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.34/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.34/7.49  --bmc1_ucm_extend_mode                  1
% 55.34/7.49  --bmc1_ucm_init_mode                    2
% 55.34/7.49  --bmc1_ucm_cone_mode                    none
% 55.34/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.34/7.49  --bmc1_ucm_relax_model                  4
% 55.34/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.34/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.34/7.49  --bmc1_ucm_layered_model                none
% 55.34/7.49  --bmc1_ucm_max_lemma_size               10
% 55.34/7.49  
% 55.34/7.49  ------ AIG Options
% 55.34/7.49  
% 55.34/7.49  --aig_mode                              false
% 55.34/7.49  
% 55.34/7.49  ------ Instantiation Options
% 55.34/7.49  
% 55.34/7.49  --instantiation_flag                    true
% 55.34/7.49  --inst_sos_flag                         false
% 55.34/7.49  --inst_sos_phase                        true
% 55.34/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.34/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.34/7.49  --inst_lit_sel_side                     num_symb
% 55.34/7.49  --inst_solver_per_active                1400
% 55.34/7.49  --inst_solver_calls_frac                1.
% 55.34/7.49  --inst_passive_queue_type               priority_queues
% 55.34/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.34/7.49  --inst_passive_queues_freq              [25;2]
% 55.34/7.49  --inst_dismatching                      true
% 55.34/7.49  --inst_eager_unprocessed_to_passive     true
% 55.34/7.49  --inst_prop_sim_given                   true
% 55.34/7.49  --inst_prop_sim_new                     false
% 55.34/7.49  --inst_subs_new                         false
% 55.34/7.49  --inst_eq_res_simp                      false
% 55.34/7.49  --inst_subs_given                       false
% 55.34/7.49  --inst_orphan_elimination               true
% 55.34/7.49  --inst_learning_loop_flag               true
% 55.34/7.49  --inst_learning_start                   3000
% 55.34/7.49  --inst_learning_factor                  2
% 55.34/7.49  --inst_start_prop_sim_after_learn       3
% 55.34/7.49  --inst_sel_renew                        solver
% 55.34/7.49  --inst_lit_activity_flag                true
% 55.34/7.49  --inst_restr_to_given                   false
% 55.34/7.49  --inst_activity_threshold               500
% 55.34/7.49  --inst_out_proof                        true
% 55.34/7.49  
% 55.34/7.49  ------ Resolution Options
% 55.34/7.49  
% 55.34/7.49  --resolution_flag                       true
% 55.34/7.49  --res_lit_sel                           adaptive
% 55.34/7.49  --res_lit_sel_side                      none
% 55.34/7.49  --res_ordering                          kbo
% 55.34/7.49  --res_to_prop_solver                    active
% 55.34/7.49  --res_prop_simpl_new                    false
% 55.34/7.49  --res_prop_simpl_given                  true
% 55.34/7.49  --res_passive_queue_type                priority_queues
% 55.34/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.34/7.49  --res_passive_queues_freq               [15;5]
% 55.34/7.49  --res_forward_subs                      full
% 55.34/7.49  --res_backward_subs                     full
% 55.34/7.49  --res_forward_subs_resolution           true
% 55.34/7.49  --res_backward_subs_resolution          true
% 55.34/7.49  --res_orphan_elimination                true
% 55.34/7.49  --res_time_limit                        2.
% 55.34/7.49  --res_out_proof                         true
% 55.34/7.49  
% 55.34/7.49  ------ Superposition Options
% 55.34/7.49  
% 55.34/7.49  --superposition_flag                    true
% 55.34/7.49  --sup_passive_queue_type                priority_queues
% 55.34/7.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.34/7.49  --sup_passive_queues_freq               [1;4]
% 55.34/7.49  --demod_completeness_check              fast
% 55.34/7.49  --demod_use_ground                      true
% 55.34/7.49  --sup_to_prop_solver                    passive
% 55.34/7.49  --sup_prop_simpl_new                    true
% 55.34/7.49  --sup_prop_simpl_given                  true
% 55.34/7.49  --sup_fun_splitting                     false
% 55.34/7.49  --sup_smt_interval                      50000
% 55.34/7.49  
% 55.34/7.49  ------ Superposition Simplification Setup
% 55.34/7.49  
% 55.34/7.49  --sup_indices_passive                   []
% 55.34/7.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.34/7.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.34/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.34/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 55.34/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.34/7.49  --sup_full_bw                           [BwDemod]
% 55.34/7.49  --sup_immed_triv                        [TrivRules]
% 55.34/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.34/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.34/7.49  --sup_immed_bw_main                     []
% 55.34/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.34/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.34/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.34/7.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.34/7.49  
% 55.34/7.49  ------ Combination Options
% 55.34/7.49  
% 55.34/7.49  --comb_res_mult                         3
% 55.34/7.49  --comb_sup_mult                         2
% 55.34/7.49  --comb_inst_mult                        10
% 55.34/7.49  
% 55.34/7.49  ------ Debug Options
% 55.34/7.49  
% 55.34/7.49  --dbg_backtrace                         false
% 55.34/7.49  --dbg_dump_prop_clauses                 false
% 55.34/7.49  --dbg_dump_prop_clauses_file            -
% 55.34/7.49  --dbg_out_stat                          false
% 55.34/7.49  
% 55.34/7.49  
% 55.34/7.49  
% 55.34/7.49  
% 55.34/7.49  ------ Proving...
% 55.34/7.49  
% 55.34/7.49  
% 55.34/7.49  % SZS status Theorem for theBenchmark.p
% 55.34/7.49  
% 55.34/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 55.34/7.49  
% 55.34/7.49  fof(f17,conjecture,(
% 55.34/7.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f18,negated_conjecture,(
% 55.34/7.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 55.34/7.49    inference(negated_conjecture,[],[f17])).
% 55.34/7.49  
% 55.34/7.49  fof(f27,plain,(
% 55.34/7.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 55.34/7.49    inference(ennf_transformation,[],[f18])).
% 55.34/7.49  
% 55.34/7.49  fof(f28,plain,(
% 55.34/7.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 55.34/7.49    inference(flattening,[],[f27])).
% 55.34/7.49  
% 55.34/7.49  fof(f32,plain,(
% 55.34/7.49    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 55.34/7.49    introduced(choice_axiom,[])).
% 55.34/7.49  
% 55.34/7.49  fof(f31,plain,(
% 55.34/7.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 55.34/7.49    introduced(choice_axiom,[])).
% 55.34/7.49  
% 55.34/7.49  fof(f33,plain,(
% 55.34/7.49    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 55.34/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32,f31])).
% 55.34/7.49  
% 55.34/7.49  fof(f56,plain,(
% 55.34/7.49    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 55.34/7.49    inference(cnf_transformation,[],[f33])).
% 55.34/7.49  
% 55.34/7.49  fof(f7,axiom,(
% 55.34/7.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f42,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f7])).
% 55.34/7.49  
% 55.34/7.49  fof(f8,axiom,(
% 55.34/7.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f43,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.34/7.49    inference(cnf_transformation,[],[f8])).
% 55.34/7.49  
% 55.34/7.49  fof(f4,axiom,(
% 55.34/7.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f39,plain,(
% 55.34/7.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.34/7.49    inference(cnf_transformation,[],[f4])).
% 55.34/7.49  
% 55.34/7.49  fof(f2,axiom,(
% 55.34/7.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f37,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.34/7.49    inference(cnf_transformation,[],[f2])).
% 55.34/7.49  
% 55.34/7.49  fof(f60,plain,(
% 55.34/7.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 55.34/7.49    inference(definition_unfolding,[],[f39,f37])).
% 55.34/7.49  
% 55.34/7.49  fof(f6,axiom,(
% 55.34/7.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f41,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f6])).
% 55.34/7.49  
% 55.34/7.49  fof(f58,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 55.34/7.49    inference(definition_unfolding,[],[f41,f37,f37])).
% 55.34/7.49  
% 55.34/7.49  fof(f3,axiom,(
% 55.34/7.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f38,plain,(
% 55.34/7.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f3])).
% 55.34/7.49  
% 55.34/7.49  fof(f59,plain,(
% 55.34/7.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 55.34/7.49    inference(definition_unfolding,[],[f38,f37])).
% 55.34/7.49  
% 55.34/7.49  fof(f5,axiom,(
% 55.34/7.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f19,plain,(
% 55.34/7.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 55.34/7.49    inference(ennf_transformation,[],[f5])).
% 55.34/7.49  
% 55.34/7.49  fof(f40,plain,(
% 55.34/7.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f19])).
% 55.34/7.49  
% 55.34/7.49  fof(f12,axiom,(
% 55.34/7.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f48,plain,(
% 55.34/7.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 55.34/7.49    inference(cnf_transformation,[],[f12])).
% 55.34/7.49  
% 55.34/7.49  fof(f13,axiom,(
% 55.34/7.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f22,plain,(
% 55.34/7.49    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 55.34/7.49    inference(ennf_transformation,[],[f13])).
% 55.34/7.49  
% 55.34/7.49  fof(f50,plain,(
% 55.34/7.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f22])).
% 55.34/7.49  
% 55.34/7.49  fof(f11,axiom,(
% 55.34/7.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f21,plain,(
% 55.34/7.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 55.34/7.49    inference(ennf_transformation,[],[f11])).
% 55.34/7.49  
% 55.34/7.49  fof(f47,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f21])).
% 55.34/7.49  
% 55.34/7.49  fof(f16,axiom,(
% 55.34/7.49    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f53,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 55.34/7.49    inference(cnf_transformation,[],[f16])).
% 55.34/7.49  
% 55.34/7.49  fof(f1,axiom,(
% 55.34/7.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f29,plain,(
% 55.34/7.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.34/7.49    inference(nnf_transformation,[],[f1])).
% 55.34/7.49  
% 55.34/7.49  fof(f30,plain,(
% 55.34/7.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.34/7.49    inference(flattening,[],[f29])).
% 55.34/7.49  
% 55.34/7.49  fof(f34,plain,(
% 55.34/7.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 55.34/7.49    inference(cnf_transformation,[],[f30])).
% 55.34/7.49  
% 55.34/7.49  fof(f62,plain,(
% 55.34/7.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.34/7.49    inference(equality_resolution,[],[f34])).
% 55.34/7.49  
% 55.34/7.49  fof(f15,axiom,(
% 55.34/7.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f25,plain,(
% 55.34/7.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 55.34/7.49    inference(ennf_transformation,[],[f15])).
% 55.34/7.49  
% 55.34/7.49  fof(f26,plain,(
% 55.34/7.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 55.34/7.49    inference(flattening,[],[f25])).
% 55.34/7.49  
% 55.34/7.49  fof(f52,plain,(
% 55.34/7.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f26])).
% 55.34/7.49  
% 55.34/7.49  fof(f36,plain,(
% 55.34/7.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f30])).
% 55.34/7.49  
% 55.34/7.49  fof(f10,axiom,(
% 55.34/7.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f45,plain,(
% 55.34/7.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 55.34/7.49    inference(cnf_transformation,[],[f10])).
% 55.34/7.49  
% 55.34/7.49  fof(f9,axiom,(
% 55.34/7.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f20,plain,(
% 55.34/7.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 55.34/7.49    inference(ennf_transformation,[],[f9])).
% 55.34/7.49  
% 55.34/7.49  fof(f44,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f20])).
% 55.34/7.49  
% 55.34/7.49  fof(f46,plain,(
% 55.34/7.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 55.34/7.49    inference(cnf_transformation,[],[f10])).
% 55.34/7.49  
% 55.34/7.49  fof(f49,plain,(
% 55.34/7.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 55.34/7.49    inference(cnf_transformation,[],[f12])).
% 55.34/7.49  
% 55.34/7.49  fof(f14,axiom,(
% 55.34/7.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 55.34/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.34/7.49  
% 55.34/7.49  fof(f23,plain,(
% 55.34/7.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 55.34/7.49    inference(ennf_transformation,[],[f14])).
% 55.34/7.49  
% 55.34/7.49  fof(f24,plain,(
% 55.34/7.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.34/7.49    inference(flattening,[],[f23])).
% 55.34/7.49  
% 55.34/7.49  fof(f51,plain,(
% 55.34/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.34/7.49    inference(cnf_transformation,[],[f24])).
% 55.34/7.49  
% 55.34/7.49  fof(f54,plain,(
% 55.34/7.49    v1_relat_1(sK0)),
% 55.34/7.49    inference(cnf_transformation,[],[f33])).
% 55.34/7.49  
% 55.34/7.49  fof(f57,plain,(
% 55.34/7.49    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 55.34/7.49    inference(cnf_transformation,[],[f33])).
% 55.34/7.49  
% 55.34/7.49  cnf(c_20,negated_conjecture,
% 55.34/7.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 55.34/7.49      inference(cnf_transformation,[],[f56]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_494,plain,
% 55.34/7.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7,plain,
% 55.34/7.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 55.34/7.49      inference(cnf_transformation,[],[f42]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_8,plain,
% 55.34/7.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 55.34/7.49      inference(cnf_transformation,[],[f43]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_704,plain,
% 55.34/7.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1108,plain,
% 55.34/7.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_704,c_8]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_5,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 55.34/7.49      inference(cnf_transformation,[],[f60]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_0,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 55.34/7.49      inference(cnf_transformation,[],[f58]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_788,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1496,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_788,c_0]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1618,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1108,c_1496]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_4,plain,
% 55.34/7.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 55.34/7.49      inference(cnf_transformation,[],[f59]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_503,plain,
% 55.34/7.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1354,plain,
% 55.34/7.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_0,c_503]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_6,plain,
% 55.34/7.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 55.34/7.49      inference(cnf_transformation,[],[f40]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_502,plain,
% 55.34/7.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1610,plain,
% 55.34/7.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1354,c_502]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1370,plain,
% 55.34/7.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1108,c_1354]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_3740,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1370,c_502]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1230,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1108,c_5]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_4174,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_1610,c_1230]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_5444,plain,
% 55.34/7.49      ( k3_xboole_0(X0,X0) = X0 ),
% 55.34/7.49      inference(light_normalisation,
% 55.34/7.49                [status(thm)],
% 55.34/7.49                [c_1618,c_1610,c_3740,c_4174]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_14,plain,
% 55.34/7.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 55.34/7.49      inference(cnf_transformation,[],[f48]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_498,plain,
% 55.34/7.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_15,plain,
% 55.34/7.49      ( ~ v1_relat_1(X0)
% 55.34/7.49      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 55.34/7.49      inference(cnf_transformation,[],[f50]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_497,plain,
% 55.34/7.49      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 55.34/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1711,plain,
% 55.34/7.49      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_498,c_497]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_12,plain,
% 55.34/7.49      ( ~ v1_relat_1(X0)
% 55.34/7.49      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 55.34/7.49      inference(cnf_transformation,[],[f47]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_500,plain,
% 55.34/7.49      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 55.34/7.49      | v1_relat_1(X1) != iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1843,plain,
% 55.34/7.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_498,c_500]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_18,plain,
% 55.34/7.49      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
% 55.34/7.49      inference(cnf_transformation,[],[f53]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1848,plain,
% 55.34/7.49      ( k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_1843,c_18]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_4939,plain,
% 55.34/7.49      ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_1711,c_1848]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_3,plain,
% 55.34/7.49      ( r1_tarski(X0,X0) ),
% 55.34/7.49      inference(cnf_transformation,[],[f62]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_504,plain,
% 55.34/7.49      ( r1_tarski(X0,X0) = iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_17,plain,
% 55.34/7.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 55.34/7.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 55.34/7.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 55.34/7.49      | ~ v1_funct_1(X1)
% 55.34/7.49      | ~ v1_relat_1(X1) ),
% 55.34/7.49      inference(cnf_transformation,[],[f52]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_495,plain,
% 55.34/7.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 55.34/7.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 55.34/7.49      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 55.34/7.49      | v1_funct_1(X1) != iProver_top
% 55.34/7.49      | v1_relat_1(X1) != iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1118,plain,
% 55.34/7.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 55.34/7.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 55.34/7.49      | v1_funct_1(X1) != iProver_top
% 55.34/7.49      | v1_relat_1(X1) != iProver_top ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_504,c_495]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1,plain,
% 55.34/7.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 55.34/7.49      inference(cnf_transformation,[],[f36]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_505,plain,
% 55.34/7.49      ( X0 = X1
% 55.34/7.49      | r1_tarski(X0,X1) != iProver_top
% 55.34/7.49      | r1_tarski(X1,X0) != iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_2647,plain,
% 55.34/7.49      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 55.34/7.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 55.34/7.49      | r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) != iProver_top
% 55.34/7.49      | v1_funct_1(X0) != iProver_top
% 55.34/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1118,c_505]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7321,plain,
% 55.34/7.49      ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),k9_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)) = X2
% 55.34/7.49      | r1_tarski(X2,k1_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2))),X2) != iProver_top
% 55.34/7.49      | v1_funct_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top
% 55.34/7.49      | v1_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_4939,c_2647]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_11,plain,
% 55.34/7.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 55.34/7.49      inference(cnf_transformation,[],[f45]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_9,plain,
% 55.34/7.49      ( ~ v1_relat_1(X0)
% 55.34/7.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 55.34/7.49      inference(cnf_transformation,[],[f44]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_501,plain,
% 55.34/7.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 55.34/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1964,plain,
% 55.34/7.49      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_498,c_501]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1969,plain,
% 55.34/7.49      ( k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_1964,c_1848]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_10,plain,
% 55.34/7.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 55.34/7.49      inference(cnf_transformation,[],[f46]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1970,plain,
% 55.34/7.49      ( k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,X1) ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_1969,c_10]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_4944,plain,
% 55.34/7.49      ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),X2)) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1108,c_4939]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7334,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) = X2
% 55.34/7.49      | r1_tarski(X2,k3_xboole_0(X0,X1)) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),k3_xboole_0(k3_xboole_0(X0,X1),X2))),X2) != iProver_top
% 55.34/7.49      | v1_funct_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top
% 55.34/7.49      | v1_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) != iProver_top ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_7321,c_11,c_1970,c_4944]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_13,plain,
% 55.34/7.49      ( v1_funct_1(k6_relat_1(X0)) ),
% 55.34/7.49      inference(cnf_transformation,[],[f49]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_499,plain,
% 55.34/7.49      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7558,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) = X2
% 55.34/7.49      | r1_tarski(X2,k3_xboole_0(X0,X1)) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),k3_xboole_0(k3_xboole_0(X0,X1),X2))),X2) != iProver_top ),
% 55.34/7.49      inference(forward_subsumption_resolution,
% 55.34/7.49                [status(thm)],
% 55.34/7.49                [c_7334,c_498,c_499]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7579,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))) = X1
% 55.34/7.49      | r1_tarski(X1,k3_xboole_0(X0,X0)) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_5444,c_7558]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7615,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) = X1
% 55.34/7.49      | r1_tarski(X1,X0) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_7579,c_5444]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_16,plain,
% 55.34/7.49      ( ~ v1_funct_1(X0)
% 55.34/7.49      | ~ v1_relat_1(X0)
% 55.34/7.49      | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 55.34/7.49      inference(cnf_transformation,[],[f51]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_496,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
% 55.34/7.49      | v1_funct_1(X1) != iProver_top
% 55.34/7.49      | v1_relat_1(X1) != iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1475,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))
% 55.34/7.49      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_499,c_496]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1483,plain,
% 55.34/7.49      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
% 55.34/7.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_1475,c_11]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_36,plain,
% 55.34/7.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_3339,plain,
% 55.34/7.49      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) ),
% 55.34/7.49      inference(global_propositional_subsumption,
% 55.34/7.49                [status(thm)],
% 55.34/7.49                [c_1483,c_36]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_3342,plain,
% 55.34/7.49      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_3339,c_1970]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_3348,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_3342,c_1970]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_6188,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_3348,c_5444]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7616,plain,
% 55.34/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = X1
% 55.34/7.49      | r1_tarski(X1,X0) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X0),X1) != iProver_top ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_7615,c_6188]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_6202,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_6188,c_0]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_6214,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_6202,c_6188]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_6805,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1108,c_6214]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7008,plain,
% 55.34/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(k10_relat_1(k6_relat_1(X0),X1),X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_6188,c_6805]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_7022,plain,
% 55.34/7.49      ( k3_xboole_0(k10_relat_1(k6_relat_1(X0),X1),X0) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_7008,c_6214]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_5474,plain,
% 55.34/7.49      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_5444,c_4939]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_75099,plain,
% 55.34/7.49      ( k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_5474,c_6188]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_163395,plain,
% 55.34/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_7022,c_75099]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_163416,plain,
% 55.34/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_1108,c_163395]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_208701,plain,
% 55.34/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = X1
% 55.34/7.49      | r1_tarski(X1,X0) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(X1,X0),X1) != iProver_top ),
% 55.34/7.49      inference(light_normalisation,[status(thm)],[c_7616,c_163416]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_208702,plain,
% 55.34/7.49      ( k3_xboole_0(X0,X1) = X0
% 55.34/7.49      | r1_tarski(X0,X1) != iProver_top
% 55.34/7.49      | r1_tarski(k3_xboole_0(X0,X1),X0) != iProver_top ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_208701,c_163416]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_208706,plain,
% 55.34/7.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 55.34/7.49      inference(forward_subsumption_resolution,
% 55.34/7.49                [status(thm)],
% 55.34/7.49                [c_208702,c_1354]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_208710,plain,
% 55.34/7.49      ( k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k10_relat_1(sK0,sK2) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_494,c_208706]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_209076,plain,
% 55.34/7.49      ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_208710,c_1108]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_22,negated_conjecture,
% 55.34/7.49      ( v1_relat_1(sK0) ),
% 55.34/7.49      inference(cnf_transformation,[],[f54]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_492,plain,
% 55.34/7.49      ( v1_relat_1(sK0) = iProver_top ),
% 55.34/7.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_1712,plain,
% 55.34/7.49      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
% 55.34/7.49      inference(superposition,[status(thm)],[c_492,c_497]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_19,negated_conjecture,
% 55.34/7.49      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 55.34/7.49      inference(cnf_transformation,[],[f57]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(c_5590,plain,
% 55.34/7.49      ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) != k10_relat_1(sK0,sK2) ),
% 55.34/7.49      inference(demodulation,[status(thm)],[c_1712,c_19]) ).
% 55.34/7.49  
% 55.34/7.49  cnf(contradiction,plain,
% 55.34/7.49      ( $false ),
% 55.34/7.49      inference(minisat,[status(thm)],[c_209076,c_5590]) ).
% 55.34/7.49  
% 55.34/7.49  
% 55.34/7.49  % SZS output end CNFRefutation for theBenchmark.p
% 55.34/7.49  
% 55.34/7.49  ------                               Statistics
% 55.34/7.49  
% 55.34/7.49  ------ Selected
% 55.34/7.49  
% 55.34/7.49  total_time:                             6.655
% 55.34/7.49  
%------------------------------------------------------------------------------
