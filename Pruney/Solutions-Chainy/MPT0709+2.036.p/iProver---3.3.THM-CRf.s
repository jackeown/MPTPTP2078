%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:41 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 765 expanded)
%              Number of clauses        :   87 ( 281 expanded)
%              Number of leaves         :   15 ( 146 expanded)
%              Depth                    :   25
%              Number of atoms          :  254 (2424 expanded)
%              Number of equality atoms :  139 ( 742 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_505,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_513,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_508,plain,
    ( k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1152,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2)) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_508])).

cnf(c_6682,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1)) = k7_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_505,c_1152])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_512,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1477,plain,
    ( k7_relat_1(sK1,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_505,c_512])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_507,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1084,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_507])).

cnf(c_4778,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_505,c_1084])).

cnf(c_4781,plain,
    ( k1_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1))) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_4778,c_1477])).

cnf(c_6685,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1)))) = k7_relat_1(sK1,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_6682,c_1477,c_4781])).

cnf(c_7190,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_6685])).

cnf(c_7251,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_7190,c_0])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_509,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1091,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_509])).

cnf(c_5644,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_505,c_1091])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_510,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1146,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_505,c_510])).

cnf(c_5647,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5644,c_1146])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_506,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_724,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_505,c_506])).

cnf(c_6311,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_5647,c_724])).

cnf(c_7197,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))))) = k7_relat_1(sK1,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_6311,c_6685])).

cnf(c_1153,plain,
    ( k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_505,c_508])).

cnf(c_1085,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_505,c_507])).

cnf(c_1154,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1153,c_1085])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_172,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_173,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_177,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_173,c_16,c_15])).

cnf(c_204,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(sK1,k9_relat_1(sK1,X1)) != X2
    | k1_relat_1(X0) != X1
    | k1_relat_1(k7_relat_1(X0,X2)) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_177])).

cnf(c_205,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0))) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_503,plain,
    ( k1_relat_1(k7_relat_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_767,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(X0,X1)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(X0,X1))))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_503])).

cnf(c_831,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_505,c_767])).

cnf(c_1350,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) ),
    inference(superposition,[status(thm)],[c_1154,c_831])).

cnf(c_1354,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(demodulation,[status(thm)],[c_1350,c_1154])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_511,plain,
    ( k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1224,plain,
    ( k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_505,c_511])).

cnf(c_1225,plain,
    ( k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1224,c_1085])).

cnf(c_1355,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1354,c_831,c_1225])).

cnf(c_1785,plain,
    ( k1_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_1355,c_1477])).

cnf(c_1796,plain,
    ( k7_relat_1(sK1,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_1785,c_1154])).

cnf(c_7243,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_7197,c_1154,c_1796])).

cnf(c_7252,plain,
    ( k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_7251,c_7243])).

cnf(c_766,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2),X3) = k3_xboole_0(X2,k10_relat_1(k7_relat_1(X0,X1),X3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_506])).

cnf(c_2072,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_505,c_766])).

cnf(c_2075,plain,
    ( k10_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
    inference(light_normalisation,[status(thm)],[c_2072,c_1477])).

cnf(c_2076,plain,
    ( k10_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))) ),
    inference(demodulation,[status(thm)],[c_2075,c_724])).

cnf(c_2800,plain,
    ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))),X1) = k3_xboole_0(X0,k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X1))) ),
    inference(superposition,[status(thm)],[c_1085,c_2076])).

cnf(c_2814,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X1))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2800,c_724,c_1154])).

cnf(c_2815,plain,
    ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X1)))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(demodulation,[status(thm)],[c_2814,c_1085])).

cnf(c_2994,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))),k10_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_2815,c_0])).

cnf(c_1352,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1154,c_724])).

cnf(c_1353,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,X1)) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1352,c_724])).

cnf(c_3498,plain,
    ( k3_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_2994,c_1353])).

cnf(c_3507,plain,
    ( k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))) = k10_relat_1(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_3498,c_0])).

cnf(c_9390,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_7252,c_3507])).

cnf(c_12,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_9393,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
    inference(demodulation,[status(thm)],[c_9390,c_12])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_189,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0,X1)) = X1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_190,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0,sK0)) = sK0 ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_504,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0,sK0)) = sK0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_591,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_504])).

cnf(c_192,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | k1_relat_1(sK1) != k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_315,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_322,plain,
    ( k1_relat_1(sK1) = k1_relat_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_309,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_326,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_594,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_16,c_192,c_322,c_326])).

cnf(c_9407,plain,
    ( sK0 != sK0 ),
    inference(light_normalisation,[status(thm)],[c_9393,c_594])).

cnf(c_9408,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9407])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:02:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.64/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/1.00  
% 3.64/1.00  ------  iProver source info
% 3.64/1.00  
% 3.64/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.64/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/1.00  git: non_committed_changes: false
% 3.64/1.00  git: last_make_outside_of_git: false
% 3.64/1.00  
% 3.64/1.00  ------ 
% 3.64/1.00  
% 3.64/1.00  ------ Input Options
% 3.64/1.00  
% 3.64/1.00  --out_options                           all
% 3.64/1.00  --tptp_safe_out                         true
% 3.64/1.00  --problem_path                          ""
% 3.64/1.00  --include_path                          ""
% 3.64/1.00  --clausifier                            res/vclausify_rel
% 3.64/1.00  --clausifier_options                    ""
% 3.64/1.00  --stdin                                 false
% 3.64/1.00  --stats_out                             all
% 3.64/1.00  
% 3.64/1.00  ------ General Options
% 3.64/1.00  
% 3.64/1.00  --fof                                   false
% 3.64/1.00  --time_out_real                         305.
% 3.64/1.00  --time_out_virtual                      -1.
% 3.64/1.00  --symbol_type_check                     false
% 3.64/1.00  --clausify_out                          false
% 3.64/1.00  --sig_cnt_out                           false
% 3.64/1.00  --trig_cnt_out                          false
% 3.64/1.00  --trig_cnt_out_tolerance                1.
% 3.64/1.00  --trig_cnt_out_sk_spl                   false
% 3.64/1.00  --abstr_cl_out                          false
% 3.64/1.00  
% 3.64/1.00  ------ Global Options
% 3.64/1.00  
% 3.64/1.00  --schedule                              default
% 3.64/1.00  --add_important_lit                     false
% 3.64/1.00  --prop_solver_per_cl                    1000
% 3.64/1.00  --min_unsat_core                        false
% 3.64/1.00  --soft_assumptions                      false
% 3.64/1.00  --soft_lemma_size                       3
% 3.64/1.00  --prop_impl_unit_size                   0
% 3.64/1.00  --prop_impl_unit                        []
% 3.64/1.00  --share_sel_clauses                     true
% 3.64/1.00  --reset_solvers                         false
% 3.64/1.00  --bc_imp_inh                            [conj_cone]
% 3.64/1.00  --conj_cone_tolerance                   3.
% 3.64/1.00  --extra_neg_conj                        none
% 3.64/1.00  --large_theory_mode                     true
% 3.64/1.00  --prolific_symb_bound                   200
% 3.64/1.00  --lt_threshold                          2000
% 3.64/1.00  --clause_weak_htbl                      true
% 3.64/1.00  --gc_record_bc_elim                     false
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing Options
% 3.64/1.00  
% 3.64/1.00  --preprocessing_flag                    true
% 3.64/1.00  --time_out_prep_mult                    0.1
% 3.64/1.00  --splitting_mode                        input
% 3.64/1.00  --splitting_grd                         true
% 3.64/1.00  --splitting_cvd                         false
% 3.64/1.00  --splitting_cvd_svl                     false
% 3.64/1.00  --splitting_nvd                         32
% 3.64/1.00  --sub_typing                            true
% 3.64/1.00  --prep_gs_sim                           true
% 3.64/1.00  --prep_unflatten                        true
% 3.64/1.00  --prep_res_sim                          true
% 3.64/1.00  --prep_upred                            true
% 3.64/1.00  --prep_sem_filter                       exhaustive
% 3.64/1.00  --prep_sem_filter_out                   false
% 3.64/1.00  --pred_elim                             true
% 3.64/1.00  --res_sim_input                         true
% 3.64/1.00  --eq_ax_congr_red                       true
% 3.64/1.00  --pure_diseq_elim                       true
% 3.64/1.00  --brand_transform                       false
% 3.64/1.00  --non_eq_to_eq                          false
% 3.64/1.00  --prep_def_merge                        true
% 3.64/1.00  --prep_def_merge_prop_impl              false
% 3.64/1.00  --prep_def_merge_mbd                    true
% 3.64/1.00  --prep_def_merge_tr_red                 false
% 3.64/1.00  --prep_def_merge_tr_cl                  false
% 3.64/1.00  --smt_preprocessing                     true
% 3.64/1.00  --smt_ac_axioms                         fast
% 3.64/1.00  --preprocessed_out                      false
% 3.64/1.00  --preprocessed_stats                    false
% 3.64/1.00  
% 3.64/1.00  ------ Abstraction refinement Options
% 3.64/1.00  
% 3.64/1.00  --abstr_ref                             []
% 3.64/1.00  --abstr_ref_prep                        false
% 3.64/1.00  --abstr_ref_until_sat                   false
% 3.64/1.00  --abstr_ref_sig_restrict                funpre
% 3.64/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/1.00  --abstr_ref_under                       []
% 3.64/1.00  
% 3.64/1.00  ------ SAT Options
% 3.64/1.00  
% 3.64/1.00  --sat_mode                              false
% 3.64/1.00  --sat_fm_restart_options                ""
% 3.64/1.00  --sat_gr_def                            false
% 3.64/1.00  --sat_epr_types                         true
% 3.64/1.00  --sat_non_cyclic_types                  false
% 3.64/1.00  --sat_finite_models                     false
% 3.64/1.00  --sat_fm_lemmas                         false
% 3.64/1.00  --sat_fm_prep                           false
% 3.64/1.00  --sat_fm_uc_incr                        true
% 3.64/1.00  --sat_out_model                         small
% 3.64/1.00  --sat_out_clauses                       false
% 3.64/1.00  
% 3.64/1.00  ------ QBF Options
% 3.64/1.00  
% 3.64/1.00  --qbf_mode                              false
% 3.64/1.00  --qbf_elim_univ                         false
% 3.64/1.00  --qbf_dom_inst                          none
% 3.64/1.00  --qbf_dom_pre_inst                      false
% 3.64/1.00  --qbf_sk_in                             false
% 3.64/1.00  --qbf_pred_elim                         true
% 3.64/1.00  --qbf_split                             512
% 3.64/1.00  
% 3.64/1.00  ------ BMC1 Options
% 3.64/1.00  
% 3.64/1.00  --bmc1_incremental                      false
% 3.64/1.00  --bmc1_axioms                           reachable_all
% 3.64/1.00  --bmc1_min_bound                        0
% 3.64/1.00  --bmc1_max_bound                        -1
% 3.64/1.00  --bmc1_max_bound_default                -1
% 3.64/1.00  --bmc1_symbol_reachability              true
% 3.64/1.00  --bmc1_property_lemmas                  false
% 3.64/1.00  --bmc1_k_induction                      false
% 3.64/1.00  --bmc1_non_equiv_states                 false
% 3.64/1.00  --bmc1_deadlock                         false
% 3.64/1.00  --bmc1_ucm                              false
% 3.64/1.00  --bmc1_add_unsat_core                   none
% 3.64/1.00  --bmc1_unsat_core_children              false
% 3.64/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/1.00  --bmc1_out_stat                         full
% 3.64/1.00  --bmc1_ground_init                      false
% 3.64/1.00  --bmc1_pre_inst_next_state              false
% 3.64/1.00  --bmc1_pre_inst_state                   false
% 3.64/1.00  --bmc1_pre_inst_reach_state             false
% 3.64/1.00  --bmc1_out_unsat_core                   false
% 3.64/1.00  --bmc1_aig_witness_out                  false
% 3.64/1.00  --bmc1_verbose                          false
% 3.64/1.00  --bmc1_dump_clauses_tptp                false
% 3.64/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.64/1.00  --bmc1_dump_file                        -
% 3.64/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.64/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.64/1.00  --bmc1_ucm_extend_mode                  1
% 3.64/1.00  --bmc1_ucm_init_mode                    2
% 3.64/1.00  --bmc1_ucm_cone_mode                    none
% 3.64/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.64/1.00  --bmc1_ucm_relax_model                  4
% 3.64/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.64/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/1.00  --bmc1_ucm_layered_model                none
% 3.64/1.00  --bmc1_ucm_max_lemma_size               10
% 3.64/1.00  
% 3.64/1.00  ------ AIG Options
% 3.64/1.00  
% 3.64/1.00  --aig_mode                              false
% 3.64/1.00  
% 3.64/1.00  ------ Instantiation Options
% 3.64/1.00  
% 3.64/1.00  --instantiation_flag                    true
% 3.64/1.00  --inst_sos_flag                         true
% 3.64/1.00  --inst_sos_phase                        true
% 3.64/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel_side                     num_symb
% 3.64/1.00  --inst_solver_per_active                1400
% 3.64/1.00  --inst_solver_calls_frac                1.
% 3.64/1.00  --inst_passive_queue_type               priority_queues
% 3.64/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/1.00  --inst_passive_queues_freq              [25;2]
% 3.64/1.00  --inst_dismatching                      true
% 3.64/1.00  --inst_eager_unprocessed_to_passive     true
% 3.64/1.00  --inst_prop_sim_given                   true
% 3.64/1.00  --inst_prop_sim_new                     false
% 3.64/1.00  --inst_subs_new                         false
% 3.64/1.00  --inst_eq_res_simp                      false
% 3.64/1.00  --inst_subs_given                       false
% 3.64/1.00  --inst_orphan_elimination               true
% 3.64/1.00  --inst_learning_loop_flag               true
% 3.64/1.00  --inst_learning_start                   3000
% 3.64/1.00  --inst_learning_factor                  2
% 3.64/1.00  --inst_start_prop_sim_after_learn       3
% 3.64/1.00  --inst_sel_renew                        solver
% 3.64/1.00  --inst_lit_activity_flag                true
% 3.64/1.00  --inst_restr_to_given                   false
% 3.64/1.00  --inst_activity_threshold               500
% 3.64/1.00  --inst_out_proof                        true
% 3.64/1.00  
% 3.64/1.00  ------ Resolution Options
% 3.64/1.00  
% 3.64/1.00  --resolution_flag                       true
% 3.64/1.00  --res_lit_sel                           adaptive
% 3.64/1.00  --res_lit_sel_side                      none
% 3.64/1.00  --res_ordering                          kbo
% 3.64/1.00  --res_to_prop_solver                    active
% 3.64/1.00  --res_prop_simpl_new                    false
% 3.64/1.00  --res_prop_simpl_given                  true
% 3.64/1.00  --res_passive_queue_type                priority_queues
% 3.64/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/1.00  --res_passive_queues_freq               [15;5]
% 3.64/1.00  --res_forward_subs                      full
% 3.64/1.00  --res_backward_subs                     full
% 3.64/1.00  --res_forward_subs_resolution           true
% 3.64/1.00  --res_backward_subs_resolution          true
% 3.64/1.00  --res_orphan_elimination                true
% 3.64/1.00  --res_time_limit                        2.
% 3.64/1.00  --res_out_proof                         true
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Options
% 3.64/1.00  
% 3.64/1.00  --superposition_flag                    true
% 3.64/1.00  --sup_passive_queue_type                priority_queues
% 3.64/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.64/1.00  --demod_completeness_check              fast
% 3.64/1.00  --demod_use_ground                      true
% 3.64/1.00  --sup_to_prop_solver                    passive
% 3.64/1.00  --sup_prop_simpl_new                    true
% 3.64/1.00  --sup_prop_simpl_given                  true
% 3.64/1.00  --sup_fun_splitting                     true
% 3.64/1.00  --sup_smt_interval                      50000
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Simplification Setup
% 3.64/1.00  
% 3.64/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.64/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_immed_triv                        [TrivRules]
% 3.64/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_bw_main                     []
% 3.64/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_input_bw                          []
% 3.64/1.00  
% 3.64/1.00  ------ Combination Options
% 3.64/1.00  
% 3.64/1.00  --comb_res_mult                         3
% 3.64/1.00  --comb_sup_mult                         2
% 3.64/1.00  --comb_inst_mult                        10
% 3.64/1.00  
% 3.64/1.00  ------ Debug Options
% 3.64/1.00  
% 3.64/1.00  --dbg_backtrace                         false
% 3.64/1.00  --dbg_dump_prop_clauses                 false
% 3.64/1.00  --dbg_dump_prop_clauses_file            -
% 3.64/1.00  --dbg_out_stat                          false
% 3.64/1.00  ------ Parsing...
% 3.64/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  ------ Proving...
% 3.64/1.00  ------ Problem Properties 
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  clauses                                 14
% 3.64/1.00  conjectures                             2
% 3.64/1.00  EPR                                     1
% 3.64/1.00  Horn                                    14
% 3.64/1.00  unary                                   3
% 3.64/1.00  binary                                  10
% 3.64/1.00  lits                                    26
% 3.64/1.00  lits eq                                 14
% 3.64/1.00  fd_pure                                 0
% 3.64/1.00  fd_pseudo                               0
% 3.64/1.00  fd_cond                                 0
% 3.64/1.00  fd_pseudo_cond                          1
% 3.64/1.00  AC symbols                              0
% 3.64/1.00  
% 3.64/1.00  ------ Schedule dynamic 5 is on 
% 3.64/1.00  
% 3.64/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ 
% 3.64/1.00  Current options:
% 3.64/1.00  ------ 
% 3.64/1.00  
% 3.64/1.00  ------ Input Options
% 3.64/1.00  
% 3.64/1.00  --out_options                           all
% 3.64/1.00  --tptp_safe_out                         true
% 3.64/1.00  --problem_path                          ""
% 3.64/1.00  --include_path                          ""
% 3.64/1.00  --clausifier                            res/vclausify_rel
% 3.64/1.00  --clausifier_options                    ""
% 3.64/1.00  --stdin                                 false
% 3.64/1.00  --stats_out                             all
% 3.64/1.00  
% 3.64/1.00  ------ General Options
% 3.64/1.00  
% 3.64/1.00  --fof                                   false
% 3.64/1.00  --time_out_real                         305.
% 3.64/1.00  --time_out_virtual                      -1.
% 3.64/1.00  --symbol_type_check                     false
% 3.64/1.00  --clausify_out                          false
% 3.64/1.00  --sig_cnt_out                           false
% 3.64/1.00  --trig_cnt_out                          false
% 3.64/1.00  --trig_cnt_out_tolerance                1.
% 3.64/1.00  --trig_cnt_out_sk_spl                   false
% 3.64/1.00  --abstr_cl_out                          false
% 3.64/1.00  
% 3.64/1.00  ------ Global Options
% 3.64/1.00  
% 3.64/1.00  --schedule                              default
% 3.64/1.00  --add_important_lit                     false
% 3.64/1.00  --prop_solver_per_cl                    1000
% 3.64/1.00  --min_unsat_core                        false
% 3.64/1.00  --soft_assumptions                      false
% 3.64/1.00  --soft_lemma_size                       3
% 3.64/1.00  --prop_impl_unit_size                   0
% 3.64/1.00  --prop_impl_unit                        []
% 3.64/1.00  --share_sel_clauses                     true
% 3.64/1.00  --reset_solvers                         false
% 3.64/1.00  --bc_imp_inh                            [conj_cone]
% 3.64/1.00  --conj_cone_tolerance                   3.
% 3.64/1.00  --extra_neg_conj                        none
% 3.64/1.00  --large_theory_mode                     true
% 3.64/1.00  --prolific_symb_bound                   200
% 3.64/1.00  --lt_threshold                          2000
% 3.64/1.00  --clause_weak_htbl                      true
% 3.64/1.00  --gc_record_bc_elim                     false
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing Options
% 3.64/1.00  
% 3.64/1.00  --preprocessing_flag                    true
% 3.64/1.00  --time_out_prep_mult                    0.1
% 3.64/1.00  --splitting_mode                        input
% 3.64/1.00  --splitting_grd                         true
% 3.64/1.00  --splitting_cvd                         false
% 3.64/1.00  --splitting_cvd_svl                     false
% 3.64/1.00  --splitting_nvd                         32
% 3.64/1.00  --sub_typing                            true
% 3.64/1.00  --prep_gs_sim                           true
% 3.64/1.00  --prep_unflatten                        true
% 3.64/1.00  --prep_res_sim                          true
% 3.64/1.00  --prep_upred                            true
% 3.64/1.00  --prep_sem_filter                       exhaustive
% 3.64/1.00  --prep_sem_filter_out                   false
% 3.64/1.00  --pred_elim                             true
% 3.64/1.00  --res_sim_input                         true
% 3.64/1.00  --eq_ax_congr_red                       true
% 3.64/1.00  --pure_diseq_elim                       true
% 3.64/1.00  --brand_transform                       false
% 3.64/1.00  --non_eq_to_eq                          false
% 3.64/1.00  --prep_def_merge                        true
% 3.64/1.00  --prep_def_merge_prop_impl              false
% 3.64/1.00  --prep_def_merge_mbd                    true
% 3.64/1.00  --prep_def_merge_tr_red                 false
% 3.64/1.00  --prep_def_merge_tr_cl                  false
% 3.64/1.00  --smt_preprocessing                     true
% 3.64/1.00  --smt_ac_axioms                         fast
% 3.64/1.00  --preprocessed_out                      false
% 3.64/1.00  --preprocessed_stats                    false
% 3.64/1.00  
% 3.64/1.00  ------ Abstraction refinement Options
% 3.64/1.00  
% 3.64/1.00  --abstr_ref                             []
% 3.64/1.00  --abstr_ref_prep                        false
% 3.64/1.00  --abstr_ref_until_sat                   false
% 3.64/1.00  --abstr_ref_sig_restrict                funpre
% 3.64/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/1.00  --abstr_ref_under                       []
% 3.64/1.00  
% 3.64/1.00  ------ SAT Options
% 3.64/1.00  
% 3.64/1.00  --sat_mode                              false
% 3.64/1.00  --sat_fm_restart_options                ""
% 3.64/1.00  --sat_gr_def                            false
% 3.64/1.00  --sat_epr_types                         true
% 3.64/1.00  --sat_non_cyclic_types                  false
% 3.64/1.00  --sat_finite_models                     false
% 3.64/1.00  --sat_fm_lemmas                         false
% 3.64/1.00  --sat_fm_prep                           false
% 3.64/1.00  --sat_fm_uc_incr                        true
% 3.64/1.00  --sat_out_model                         small
% 3.64/1.00  --sat_out_clauses                       false
% 3.64/1.00  
% 3.64/1.00  ------ QBF Options
% 3.64/1.00  
% 3.64/1.00  --qbf_mode                              false
% 3.64/1.00  --qbf_elim_univ                         false
% 3.64/1.00  --qbf_dom_inst                          none
% 3.64/1.00  --qbf_dom_pre_inst                      false
% 3.64/1.00  --qbf_sk_in                             false
% 3.64/1.00  --qbf_pred_elim                         true
% 3.64/1.00  --qbf_split                             512
% 3.64/1.00  
% 3.64/1.00  ------ BMC1 Options
% 3.64/1.00  
% 3.64/1.00  --bmc1_incremental                      false
% 3.64/1.00  --bmc1_axioms                           reachable_all
% 3.64/1.00  --bmc1_min_bound                        0
% 3.64/1.00  --bmc1_max_bound                        -1
% 3.64/1.00  --bmc1_max_bound_default                -1
% 3.64/1.00  --bmc1_symbol_reachability              true
% 3.64/1.00  --bmc1_property_lemmas                  false
% 3.64/1.00  --bmc1_k_induction                      false
% 3.64/1.00  --bmc1_non_equiv_states                 false
% 3.64/1.00  --bmc1_deadlock                         false
% 3.64/1.00  --bmc1_ucm                              false
% 3.64/1.00  --bmc1_add_unsat_core                   none
% 3.64/1.00  --bmc1_unsat_core_children              false
% 3.64/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/1.00  --bmc1_out_stat                         full
% 3.64/1.00  --bmc1_ground_init                      false
% 3.64/1.00  --bmc1_pre_inst_next_state              false
% 3.64/1.00  --bmc1_pre_inst_state                   false
% 3.64/1.00  --bmc1_pre_inst_reach_state             false
% 3.64/1.00  --bmc1_out_unsat_core                   false
% 3.64/1.00  --bmc1_aig_witness_out                  false
% 3.64/1.00  --bmc1_verbose                          false
% 3.64/1.00  --bmc1_dump_clauses_tptp                false
% 3.64/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.64/1.00  --bmc1_dump_file                        -
% 3.64/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.64/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.64/1.00  --bmc1_ucm_extend_mode                  1
% 3.64/1.00  --bmc1_ucm_init_mode                    2
% 3.64/1.00  --bmc1_ucm_cone_mode                    none
% 3.64/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.64/1.00  --bmc1_ucm_relax_model                  4
% 3.64/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.64/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/1.00  --bmc1_ucm_layered_model                none
% 3.64/1.00  --bmc1_ucm_max_lemma_size               10
% 3.64/1.00  
% 3.64/1.00  ------ AIG Options
% 3.64/1.00  
% 3.64/1.00  --aig_mode                              false
% 3.64/1.00  
% 3.64/1.00  ------ Instantiation Options
% 3.64/1.00  
% 3.64/1.00  --instantiation_flag                    true
% 3.64/1.00  --inst_sos_flag                         true
% 3.64/1.00  --inst_sos_phase                        true
% 3.64/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/1.00  --inst_lit_sel_side                     none
% 3.64/1.00  --inst_solver_per_active                1400
% 3.64/1.00  --inst_solver_calls_frac                1.
% 3.64/1.00  --inst_passive_queue_type               priority_queues
% 3.64/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/1.00  --inst_passive_queues_freq              [25;2]
% 3.64/1.00  --inst_dismatching                      true
% 3.64/1.00  --inst_eager_unprocessed_to_passive     true
% 3.64/1.00  --inst_prop_sim_given                   true
% 3.64/1.00  --inst_prop_sim_new                     false
% 3.64/1.00  --inst_subs_new                         false
% 3.64/1.00  --inst_eq_res_simp                      false
% 3.64/1.00  --inst_subs_given                       false
% 3.64/1.00  --inst_orphan_elimination               true
% 3.64/1.00  --inst_learning_loop_flag               true
% 3.64/1.00  --inst_learning_start                   3000
% 3.64/1.00  --inst_learning_factor                  2
% 3.64/1.00  --inst_start_prop_sim_after_learn       3
% 3.64/1.00  --inst_sel_renew                        solver
% 3.64/1.00  --inst_lit_activity_flag                true
% 3.64/1.00  --inst_restr_to_given                   false
% 3.64/1.00  --inst_activity_threshold               500
% 3.64/1.00  --inst_out_proof                        true
% 3.64/1.00  
% 3.64/1.00  ------ Resolution Options
% 3.64/1.00  
% 3.64/1.00  --resolution_flag                       false
% 3.64/1.00  --res_lit_sel                           adaptive
% 3.64/1.00  --res_lit_sel_side                      none
% 3.64/1.00  --res_ordering                          kbo
% 3.64/1.00  --res_to_prop_solver                    active
% 3.64/1.00  --res_prop_simpl_new                    false
% 3.64/1.00  --res_prop_simpl_given                  true
% 3.64/1.00  --res_passive_queue_type                priority_queues
% 3.64/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/1.00  --res_passive_queues_freq               [15;5]
% 3.64/1.00  --res_forward_subs                      full
% 3.64/1.00  --res_backward_subs                     full
% 3.64/1.00  --res_forward_subs_resolution           true
% 3.64/1.00  --res_backward_subs_resolution          true
% 3.64/1.00  --res_orphan_elimination                true
% 3.64/1.00  --res_time_limit                        2.
% 3.64/1.00  --res_out_proof                         true
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Options
% 3.64/1.00  
% 3.64/1.00  --superposition_flag                    true
% 3.64/1.00  --sup_passive_queue_type                priority_queues
% 3.64/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.64/1.00  --demod_completeness_check              fast
% 3.64/1.00  --demod_use_ground                      true
% 3.64/1.00  --sup_to_prop_solver                    passive
% 3.64/1.00  --sup_prop_simpl_new                    true
% 3.64/1.00  --sup_prop_simpl_given                  true
% 3.64/1.00  --sup_fun_splitting                     true
% 3.64/1.00  --sup_smt_interval                      50000
% 3.64/1.00  
% 3.64/1.00  ------ Superposition Simplification Setup
% 3.64/1.00  
% 3.64/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.64/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.64/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.64/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_immed_triv                        [TrivRules]
% 3.64/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_immed_bw_main                     []
% 3.64/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.64/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/1.00  --sup_input_bw                          []
% 3.64/1.00  
% 3.64/1.00  ------ Combination Options
% 3.64/1.00  
% 3.64/1.00  --comb_res_mult                         3
% 3.64/1.00  --comb_sup_mult                         2
% 3.64/1.00  --comb_inst_mult                        10
% 3.64/1.00  
% 3.64/1.00  ------ Debug Options
% 3.64/1.00  
% 3.64/1.00  --dbg_backtrace                         false
% 3.64/1.00  --dbg_dump_prop_clauses                 false
% 3.64/1.00  --dbg_dump_prop_clauses_file            -
% 3.64/1.00  --dbg_out_stat                          false
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS status Theorem for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00   Resolution empty clause
% 3.64/1.00  
% 3.64/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  fof(f1,axiom,(
% 3.64/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f15,plain,(
% 3.64/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.64/1.00    inference(rectify,[],[f1])).
% 3.64/1.00  
% 3.64/1.00  fof(f33,plain,(
% 3.64/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.64/1.00    inference(cnf_transformation,[],[f15])).
% 3.64/1.00  
% 3.64/1.00  fof(f13,conjecture,(
% 3.64/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f14,negated_conjecture,(
% 3.64/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.64/1.00    inference(negated_conjecture,[],[f13])).
% 3.64/1.00  
% 3.64/1.00  fof(f29,plain,(
% 3.64/1.00    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.64/1.00    inference(ennf_transformation,[],[f14])).
% 3.64/1.00  
% 3.64/1.00  fof(f30,plain,(
% 3.64/1.00    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.64/1.00    inference(flattening,[],[f29])).
% 3.64/1.00  
% 3.64/1.00  fof(f31,plain,(
% 3.64/1.00    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.64/1.00    introduced(choice_axiom,[])).
% 3.64/1.00  
% 3.64/1.00  fof(f32,plain,(
% 3.64/1.00    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 3.64/1.00  
% 3.64/1.00  fof(f45,plain,(
% 3.64/1.00    v1_relat_1(sK1)),
% 3.64/1.00    inference(cnf_transformation,[],[f32])).
% 3.64/1.00  
% 3.64/1.00  fof(f3,axiom,(
% 3.64/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f17,plain,(
% 3.64/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.64/1.00    inference(ennf_transformation,[],[f3])).
% 3.64/1.00  
% 3.64/1.00  fof(f35,plain,(
% 3.64/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f17])).
% 3.64/1.00  
% 3.64/1.00  fof(f8,axiom,(
% 3.64/1.00    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f22,plain,(
% 3.64/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f8])).
% 3.64/1.00  
% 3.64/1.00  fof(f40,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f22])).
% 3.64/1.00  
% 3.64/1.00  fof(f4,axiom,(
% 3.64/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f18,plain,(
% 3.64/1.00    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.64/1.00    inference(ennf_transformation,[],[f4])).
% 3.64/1.00  
% 3.64/1.00  fof(f36,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f18])).
% 3.64/1.00  
% 3.64/1.00  fof(f9,axiom,(
% 3.64/1.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f23,plain,(
% 3.64/1.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f9])).
% 3.64/1.00  
% 3.64/1.00  fof(f41,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f23])).
% 3.64/1.00  
% 3.64/1.00  fof(f7,axiom,(
% 3.64/1.00    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f21,plain,(
% 3.64/1.00    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.64/1.00    inference(ennf_transformation,[],[f7])).
% 3.64/1.00  
% 3.64/1.00  fof(f39,plain,(
% 3.64/1.00    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f21])).
% 3.64/1.00  
% 3.64/1.00  fof(f6,axiom,(
% 3.64/1.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f20,plain,(
% 3.64/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f6])).
% 3.64/1.00  
% 3.64/1.00  fof(f38,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f20])).
% 3.64/1.00  
% 3.64/1.00  fof(f11,axiom,(
% 3.64/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f26,plain,(
% 3.64/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.64/1.00    inference(ennf_transformation,[],[f11])).
% 3.64/1.00  
% 3.64/1.00  fof(f43,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f26])).
% 3.64/1.00  
% 3.64/1.00  fof(f10,axiom,(
% 3.64/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f24,plain,(
% 3.64/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f10])).
% 3.64/1.00  
% 3.64/1.00  fof(f25,plain,(
% 3.64/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.64/1.00    inference(flattening,[],[f24])).
% 3.64/1.00  
% 3.64/1.00  fof(f42,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f25])).
% 3.64/1.00  
% 3.64/1.00  fof(f12,axiom,(
% 3.64/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f27,plain,(
% 3.64/1.00    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.64/1.00    inference(ennf_transformation,[],[f12])).
% 3.64/1.00  
% 3.64/1.00  fof(f28,plain,(
% 3.64/1.00    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.64/1.00    inference(flattening,[],[f27])).
% 3.64/1.00  
% 3.64/1.00  fof(f44,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f28])).
% 3.64/1.00  
% 3.64/1.00  fof(f48,plain,(
% 3.64/1.00    v2_funct_1(sK1)),
% 3.64/1.00    inference(cnf_transformation,[],[f32])).
% 3.64/1.00  
% 3.64/1.00  fof(f46,plain,(
% 3.64/1.00    v1_funct_1(sK1)),
% 3.64/1.00    inference(cnf_transformation,[],[f32])).
% 3.64/1.00  
% 3.64/1.00  fof(f5,axiom,(
% 3.64/1.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.64/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f19,plain,(
% 3.64/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f5])).
% 3.64/1.00  
% 3.64/1.00  fof(f37,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f19])).
% 3.64/1.00  
% 3.64/1.00  fof(f49,plain,(
% 3.64/1.00    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 3.64/1.00    inference(cnf_transformation,[],[f32])).
% 3.64/1.00  
% 3.64/1.00  fof(f47,plain,(
% 3.64/1.00    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.64/1.00    inference(cnf_transformation,[],[f32])).
% 3.64/1.00  
% 3.64/1.00  cnf(c_0,plain,
% 3.64/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_16,negated_conjecture,
% 3.64/1.00      ( v1_relat_1(sK1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_505,plain,
% 3.64/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_513,plain,
% 3.64/1.00      ( v1_relat_1(X0) != iProver_top
% 3.64/1.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_508,plain,
% 3.64/1.00      ( k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1152,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(X0,X1),k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2)) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_513,c_508]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6682,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1)) = k7_relat_1(k7_relat_1(sK1,X0),X1) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_1152]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_3,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_512,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2))
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1477,plain,
% 3.64/1.00      ( k7_relat_1(sK1,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK1,X0),X1) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_512]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_8,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_507,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1084,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2)
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_513,c_507]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_4778,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_1084]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_4781,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1))) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_4778,c_1477]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6685,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1)))) = k7_relat_1(sK1,k3_xboole_0(X0,X1)) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_6682,c_1477,c_4781]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7190,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k3_xboole_0(X0,X0)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_0,c_6685]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7251,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_7190,c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_509,plain,
% 3.64/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1091,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_513,c_509]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5644,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_1091]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_510,plain,
% 3.64/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1146,plain,
% 3.64/1.00      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_510]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5647,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_5644,c_1146]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_10,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_506,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_724,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_506]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6311,plain,
% 3.64/1.00      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_5647,c_724]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7197,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))))) = k7_relat_1(sK1,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_6311,c_6685]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1153,plain,
% 3.64/1.00      ( k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,X0) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_508]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1085,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_507]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1154,plain,
% 3.64/1.00      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_1153,c_1085]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.64/1.00      | ~ v1_relat_1(X1)
% 3.64/1.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_11,plain,
% 3.64/1.00      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 3.64/1.00      | ~ v1_funct_1(X0)
% 3.64/1.00      | ~ v2_funct_1(X0)
% 3.64/1.00      | ~ v1_relat_1(X0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_13,negated_conjecture,
% 3.64/1.00      ( v2_funct_1(sK1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_172,plain,
% 3.64/1.00      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 3.64/1.00      | ~ v1_funct_1(X0)
% 3.64/1.00      | ~ v1_relat_1(X0)
% 3.64/1.00      | sK1 != X0 ),
% 3.64/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_173,plain,
% 3.64/1.00      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
% 3.64/1.00      | ~ v1_funct_1(sK1)
% 3.64/1.00      | ~ v1_relat_1(sK1) ),
% 3.64/1.00      inference(unflattening,[status(thm)],[c_172]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_15,negated_conjecture,
% 3.64/1.00      ( v1_funct_1(sK1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_177,plain,
% 3.64/1.00      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
% 3.64/1.00      inference(global_propositional_subsumption,
% 3.64/1.00                [status(thm)],
% 3.64/1.00                [c_173,c_16,c_15]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_204,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k10_relat_1(sK1,k9_relat_1(sK1,X1)) != X2
% 3.64/1.00      | k1_relat_1(X0) != X1
% 3.64/1.00      | k1_relat_1(k7_relat_1(X0,X2)) = X2 ),
% 3.64/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_177]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_205,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k1_relat_1(k7_relat_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0))) ),
% 3.64/1.00      inference(unflattening,[status(thm)],[c_204]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_503,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(X0)))
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_205]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_767,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(X0,X1)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(X0,X1))))
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_513,c_503]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_831,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_767]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1350,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_1154,c_831]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1354,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_1350,c_1154]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_4,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k9_relat_1(X0,X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_511,plain,
% 3.64/1.00      ( k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k9_relat_1(X0,X1)
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1224,plain,
% 3.64/1.00      ( k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) = k9_relat_1(sK1,X0) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_511]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1225,plain,
% 3.64/1.00      ( k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,X0) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_1224,c_1085]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1355,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_1354,c_831,c_1225]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1785,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))) = k10_relat_1(sK1,k9_relat_1(sK1,X0)) ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_1355,c_1477]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1796,plain,
% 3.64/1.00      ( k7_relat_1(sK1,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) = k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_1785,c_1154]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7243,plain,
% 3.64/1.00      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_7197,c_1154,c_1796]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7252,plain,
% 3.64/1.00      ( k7_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_7251,c_7243]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_766,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2),X3) = k3_xboole_0(X2,k10_relat_1(k7_relat_1(X0,X1),X3))
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_513,c_506]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2072,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_505,c_766]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2075,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_2072,c_1477]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2076,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(sK1,k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))) ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_2075,c_724]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2800,plain,
% 3.64/1.00      ( k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))),X1) = k3_xboole_0(X0,k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X1))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_1085,c_2076]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2814,plain,
% 3.64/1.00      ( k3_xboole_0(X0,k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X1))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_2800,c_724,c_1154]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2815,plain,
% 3.64/1.00      ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X1)))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_2814,c_1085]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_2994,plain,
% 3.64/1.00      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))),k10_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_2815,c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1352,plain,
% 3.64/1.00      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_1154,c_724]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1353,plain,
% 3.64/1.00      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,X1)) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_1352,c_724]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_3498,plain,
% 3.64/1.00      ( k3_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_2994,c_1353]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_3507,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,X0))) = k10_relat_1(sK1,X0) ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_3498,c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9390,plain,
% 3.64/1.00      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_7252,c_3507]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_12,negated_conjecture,
% 3.64/1.00      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9393,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_9390,c_12]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_14,negated_conjecture,
% 3.64/1.00      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_189,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k1_relat_1(X0) != k1_relat_1(sK1)
% 3.64/1.00      | k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.64/1.00      | sK0 != X1 ),
% 3.64/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_190,plain,
% 3.64/1.00      ( ~ v1_relat_1(X0)
% 3.64/1.00      | k1_relat_1(X0) != k1_relat_1(sK1)
% 3.64/1.00      | k1_relat_1(k7_relat_1(X0,sK0)) = sK0 ),
% 3.64/1.00      inference(unflattening,[status(thm)],[c_189]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_504,plain,
% 3.64/1.00      ( k1_relat_1(X0) != k1_relat_1(sK1)
% 3.64/1.00      | k1_relat_1(k7_relat_1(X0,sK0)) = sK0
% 3.64/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_591,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 3.64/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.64/1.00      inference(equality_resolution,[status(thm)],[c_504]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_192,plain,
% 3.64/1.00      ( ~ v1_relat_1(sK1)
% 3.64/1.00      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 3.64/1.00      | k1_relat_1(sK1) != k1_relat_1(sK1) ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_190]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_315,plain,
% 3.64/1.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.64/1.00      theory(equality) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_322,plain,
% 3.64/1.00      ( k1_relat_1(sK1) = k1_relat_1(sK1) | sK1 != sK1 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_315]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_309,plain,( X0 = X0 ),theory(equality) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_326,plain,
% 3.64/1.00      ( sK1 = sK1 ),
% 3.64/1.00      inference(instantiation,[status(thm)],[c_309]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_594,plain,
% 3.64/1.00      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.64/1.00      inference(global_propositional_subsumption,
% 3.64/1.00                [status(thm)],
% 3.64/1.00                [c_591,c_16,c_192,c_322,c_326]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9407,plain,
% 3.64/1.00      ( sK0 != sK0 ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_9393,c_594]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9408,plain,
% 3.64/1.00      ( $false ),
% 3.64/1.00      inference(equality_resolution_simp,[status(thm)],[c_9407]) ).
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  ------                               Statistics
% 3.64/1.00  
% 3.64/1.00  ------ General
% 3.64/1.00  
% 3.64/1.00  abstr_ref_over_cycles:                  0
% 3.64/1.00  abstr_ref_under_cycles:                 0
% 3.64/1.00  gc_basic_clause_elim:                   0
% 3.64/1.00  forced_gc_time:                         0
% 3.64/1.00  parsing_time:                           0.015
% 3.64/1.00  unif_index_cands_time:                  0.
% 3.64/1.00  unif_index_add_time:                    0.
% 3.64/1.00  orderings_time:                         0.
% 3.64/1.00  out_proof_time:                         0.017
% 3.64/1.00  total_time:                             0.491
% 3.64/1.00  num_of_symbols:                         44
% 3.64/1.00  num_of_terms:                           14758
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing
% 3.64/1.00  
% 3.64/1.00  num_of_splits:                          0
% 3.64/1.00  num_of_split_atoms:                     0
% 3.64/1.00  num_of_reused_defs:                     0
% 3.64/1.00  num_eq_ax_congr_red:                    3
% 3.64/1.00  num_of_sem_filtered_clauses:            1
% 3.64/1.00  num_of_subtypes:                        0
% 3.64/1.00  monotx_restored_types:                  0
% 3.64/1.00  sat_num_of_epr_types:                   0
% 3.64/1.00  sat_num_of_non_cyclic_types:            0
% 3.64/1.00  sat_guarded_non_collapsed_types:        0
% 3.64/1.00  num_pure_diseq_elim:                    0
% 3.64/1.00  simp_replaced_by:                       0
% 3.64/1.00  res_preprocessed:                       78
% 3.64/1.00  prep_upred:                             0
% 3.64/1.00  prep_unflattend:                        4
% 3.64/1.00  smt_new_axioms:                         0
% 3.64/1.00  pred_elim_cands:                        1
% 3.64/1.00  pred_elim:                              3
% 3.64/1.00  pred_elim_cl:                           3
% 3.64/1.00  pred_elim_cycles:                       5
% 3.64/1.00  merged_defs:                            0
% 3.64/1.00  merged_defs_ncl:                        0
% 3.64/1.00  bin_hyper_res:                          0
% 3.64/1.00  prep_cycles:                            4
% 3.64/1.00  pred_elim_time:                         0.001
% 3.64/1.00  splitting_time:                         0.
% 3.64/1.00  sem_filter_time:                        0.
% 3.64/1.00  monotx_time:                            0.
% 3.64/1.00  subtype_inf_time:                       0.
% 3.64/1.00  
% 3.64/1.00  ------ Problem properties
% 3.64/1.00  
% 3.64/1.00  clauses:                                14
% 3.64/1.00  conjectures:                            2
% 3.64/1.00  epr:                                    1
% 3.64/1.00  horn:                                   14
% 3.64/1.00  ground:                                 2
% 3.64/1.00  unary:                                  3
% 3.64/1.00  binary:                                 10
% 3.64/1.00  lits:                                   26
% 3.64/1.00  lits_eq:                                14
% 3.64/1.00  fd_pure:                                0
% 3.64/1.00  fd_pseudo:                              0
% 3.64/1.00  fd_cond:                                0
% 3.64/1.00  fd_pseudo_cond:                         1
% 3.64/1.00  ac_symbols:                             0
% 3.64/1.00  
% 3.64/1.00  ------ Propositional Solver
% 3.64/1.00  
% 3.64/1.00  prop_solver_calls:                      35
% 3.64/1.00  prop_fast_solver_calls:                 481
% 3.64/1.00  smt_solver_calls:                       0
% 3.64/1.00  smt_fast_solver_calls:                  0
% 3.64/1.00  prop_num_of_clauses:                    3559
% 3.64/1.00  prop_preprocess_simplified:             5968
% 3.64/1.00  prop_fo_subsumed:                       3
% 3.64/1.00  prop_solver_time:                       0.
% 3.64/1.00  smt_solver_time:                        0.
% 3.64/1.00  smt_fast_solver_time:                   0.
% 3.64/1.00  prop_fast_solver_time:                  0.
% 3.64/1.00  prop_unsat_core_time:                   0.
% 3.64/1.00  
% 3.64/1.00  ------ QBF
% 3.64/1.00  
% 3.64/1.00  qbf_q_res:                              0
% 3.64/1.00  qbf_num_tautologies:                    0
% 3.64/1.00  qbf_prep_cycles:                        0
% 3.64/1.00  
% 3.64/1.00  ------ BMC1
% 3.64/1.00  
% 3.64/1.00  bmc1_current_bound:                     -1
% 3.64/1.00  bmc1_last_solved_bound:                 -1
% 3.64/1.00  bmc1_unsat_core_size:                   -1
% 3.64/1.00  bmc1_unsat_core_parents_size:           -1
% 3.64/1.00  bmc1_merge_next_fun:                    0
% 3.64/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.64/1.00  
% 3.64/1.00  ------ Instantiation
% 3.64/1.00  
% 3.64/1.00  inst_num_of_clauses:                    1362
% 3.64/1.00  inst_num_in_passive:                    339
% 3.64/1.00  inst_num_in_active:                     483
% 3.64/1.00  inst_num_in_unprocessed:                542
% 3.64/1.00  inst_num_of_loops:                      520
% 3.64/1.00  inst_num_of_learning_restarts:          0
% 3.64/1.00  inst_num_moves_active_passive:          31
% 3.64/1.00  inst_lit_activity:                      0
% 3.64/1.00  inst_lit_activity_moves:                0
% 3.64/1.00  inst_num_tautologies:                   0
% 3.64/1.00  inst_num_prop_implied:                  0
% 3.64/1.00  inst_num_existing_simplified:           0
% 3.64/1.00  inst_num_eq_res_simplified:             0
% 3.64/1.00  inst_num_child_elim:                    0
% 3.64/1.00  inst_num_of_dismatching_blockings:      568
% 3.64/1.00  inst_num_of_non_proper_insts:           1831
% 3.64/1.00  inst_num_of_duplicates:                 0
% 3.64/1.00  inst_inst_num_from_inst_to_res:         0
% 3.64/1.00  inst_dismatching_checking_time:         0.
% 3.64/1.00  
% 3.64/1.00  ------ Resolution
% 3.64/1.00  
% 3.64/1.00  res_num_of_clauses:                     0
% 3.64/1.00  res_num_in_passive:                     0
% 3.64/1.00  res_num_in_active:                      0
% 3.64/1.00  res_num_of_loops:                       82
% 3.64/1.00  res_forward_subset_subsumed:            149
% 3.64/1.00  res_backward_subset_subsumed:           6
% 3.64/1.00  res_forward_subsumed:                   0
% 3.64/1.00  res_backward_subsumed:                  0
% 3.64/1.00  res_forward_subsumption_resolution:     0
% 3.64/1.00  res_backward_subsumption_resolution:    0
% 3.64/1.00  res_clause_to_clause_subsumption:       2402
% 3.64/1.00  res_orphan_elimination:                 0
% 3.64/1.00  res_tautology_del:                      214
% 3.64/1.00  res_num_eq_res_simplified:              0
% 3.64/1.00  res_num_sel_changes:                    0
% 3.64/1.00  res_moves_from_active_to_pass:          0
% 3.64/1.00  
% 3.64/1.00  ------ Superposition
% 3.64/1.00  
% 3.64/1.00  sup_time_total:                         0.
% 3.64/1.00  sup_time_generating:                    0.
% 3.64/1.00  sup_time_sim_full:                      0.
% 3.64/1.00  sup_time_sim_immed:                     0.
% 3.64/1.00  
% 3.64/1.00  sup_num_of_clauses:                     466
% 3.64/1.00  sup_num_in_active:                      73
% 3.64/1.00  sup_num_in_passive:                     393
% 3.64/1.00  sup_num_of_loops:                       103
% 3.64/1.00  sup_fw_superposition:                   859
% 3.64/1.00  sup_bw_superposition:                   702
% 3.64/1.00  sup_immediate_simplified:               1515
% 3.64/1.00  sup_given_eliminated:                   3
% 3.64/1.00  comparisons_done:                       0
% 3.64/1.00  comparisons_avoided:                    0
% 3.64/1.00  
% 3.64/1.00  ------ Simplifications
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  sim_fw_subset_subsumed:                 0
% 3.64/1.00  sim_bw_subset_subsumed:                 2
% 3.64/1.00  sim_fw_subsumed:                        161
% 3.64/1.00  sim_bw_subsumed:                        1
% 3.64/1.00  sim_fw_subsumption_res:                 0
% 3.64/1.00  sim_bw_subsumption_res:                 0
% 3.64/1.00  sim_tautology_del:                      11
% 3.64/1.00  sim_eq_tautology_del:                   570
% 3.64/1.00  sim_eq_res_simp:                        0
% 3.64/1.00  sim_fw_demodulated:                     917
% 3.64/1.00  sim_bw_demodulated:                     42
% 3.64/1.00  sim_light_normalised:                   845
% 3.64/1.00  sim_joinable_taut:                      0
% 3.64/1.00  sim_joinable_simp:                      0
% 3.64/1.00  sim_ac_normalised:                      0
% 3.64/1.00  sim_smt_subsumption:                    0
% 3.64/1.00  
%------------------------------------------------------------------------------
