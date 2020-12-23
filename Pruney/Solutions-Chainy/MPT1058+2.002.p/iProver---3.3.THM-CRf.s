%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:12 EST 2020

% Result     : Theorem 51.46s
% Output     : CNFRefutation 51.46s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 153 expanded)
%              Number of clauses        :   36 (  40 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  215 ( 408 expanded)
%              Number of equality atoms :   69 ( 134 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f89,f90])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f88,f118])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f87,f119])).

fof(f121,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f86,f120])).

fof(f122,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f85,f121])).

fof(f123,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f91,f122])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f123])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f106,f123])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4)
        & r1_tarski(k10_relat_1(X0,sK4),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2)
          & r1_tarski(k10_relat_1(sK2,X2),X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    & r1_tarski(k10_relat_1(sK2,sK4),sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f70,f69])).

fof(f117,plain,(
    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f71])).

fof(f114,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f132,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f116,plain,(
    r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_185319,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK4),X0)
    | ~ r1_tarski(k10_relat_1(sK2,sK4),X1)
    | r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_189732,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK4),X0)
    | ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4))
    | r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_185319])).

cnf(c_199862,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4))
    | r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))))
    | ~ r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_189732])).

cnf(c_626,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1558,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X1
    | k10_relat_1(sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_26042,plain,
    ( ~ r1_tarski(X0,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))))
    | r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4)))
    | k10_relat_1(sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_55192,plain,
    ( r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
    | ~ r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))))
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4)))
    | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_26042])).

cnf(c_27,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_11446,plain,
    ( ~ v1_relat_1(sK2)
    | k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_624,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1810,plain,
    ( X0 != X1
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X1
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_4903,plain,
    ( X0 != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_11445,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4)))
    | k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_4903])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_10228,plain,
    ( r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(X0,sK4))
    | ~ r1_tarski(sK2,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_10232,plain,
    ( r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4))
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10228])).

cnf(c_18,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4764,plain,
    ( r1_tarski(k7_relat_1(sK2,sK3),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,negated_conjecture,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2553,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),k10_relat_1(sK2,sK4))
    | ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4)) ),
    inference(resolution,[status(thm)],[c_4,c_34])).

cnf(c_4379,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
    | ~ r1_tarski(k7_relat_1(sK2,sK3),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_17,c_2553])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1774,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4382,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
    | ~ r1_tarski(k7_relat_1(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4379,c_37,c_1774])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2570,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1794,plain,
    ( ~ r1_tarski(X0,k10_relat_1(k7_relat_1(sK2,sK3),sK4))
    | ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),X0)
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2569,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
    | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_623,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1608,plain,
    ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_117,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f116])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_199862,c_55192,c_11446,c_11445,c_10232,c_4764,c_4382,c_2570,c_2569,c_1608,c_117,c_35,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.46/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.46/7.00  
% 51.46/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.46/7.00  
% 51.46/7.00  ------  iProver source info
% 51.46/7.00  
% 51.46/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.46/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.46/7.00  git: non_committed_changes: false
% 51.46/7.00  git: last_make_outside_of_git: false
% 51.46/7.00  
% 51.46/7.00  ------ 
% 51.46/7.00  ------ Parsing...
% 51.46/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.46/7.00  
% 51.46/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.46/7.00  
% 51.46/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.46/7.00  
% 51.46/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.46/7.00  ------ Proving...
% 51.46/7.00  ------ Problem Properties 
% 51.46/7.00  
% 51.46/7.00  
% 51.46/7.00  clauses                                 36
% 51.46/7.00  conjectures                             4
% 51.46/7.00  EPR                                     7
% 51.46/7.00  Horn                                    33
% 51.46/7.00  unary                                   9
% 51.46/7.00  binary                                  13
% 51.46/7.00  lits                                    91
% 51.46/7.00  lits eq                                 14
% 51.46/7.00  fd_pure                                 0
% 51.46/7.00  fd_pseudo                               0
% 51.46/7.00  fd_cond                                 3
% 51.46/7.00  fd_pseudo_cond                          4
% 51.46/7.00  AC symbols                              0
% 51.46/7.00  
% 51.46/7.00  ------ Input Options Time Limit: Unbounded
% 51.46/7.00  
% 51.46/7.00  
% 51.46/7.00  ------ 
% 51.46/7.00  Current options:
% 51.46/7.00  ------ 
% 51.46/7.00  
% 51.46/7.00  
% 51.46/7.00  
% 51.46/7.00  
% 51.46/7.00  ------ Proving...
% 51.46/7.00  
% 51.46/7.00  
% 51.46/7.00  % SZS status Theorem for theBenchmark.p
% 51.46/7.00  
% 51.46/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.46/7.00  
% 51.46/7.00  fof(f7,axiom,(
% 51.46/7.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f36,plain,(
% 51.46/7.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 51.46/7.00    inference(ennf_transformation,[],[f7])).
% 51.46/7.00  
% 51.46/7.00  fof(f37,plain,(
% 51.46/7.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 51.46/7.00    inference(flattening,[],[f36])).
% 51.46/7.00  
% 51.46/7.00  fof(f82,plain,(
% 51.46/7.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f37])).
% 51.46/7.00  
% 51.46/7.00  fof(f16,axiom,(
% 51.46/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f91,plain,(
% 51.46/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 51.46/7.00    inference(cnf_transformation,[],[f16])).
% 51.46/7.00  
% 51.46/7.00  fof(f10,axiom,(
% 51.46/7.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f85,plain,(
% 51.46/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f10])).
% 51.46/7.00  
% 51.46/7.00  fof(f11,axiom,(
% 51.46/7.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f86,plain,(
% 51.46/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f11])).
% 51.46/7.00  
% 51.46/7.00  fof(f12,axiom,(
% 51.46/7.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f87,plain,(
% 51.46/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f12])).
% 51.46/7.00  
% 51.46/7.00  fof(f13,axiom,(
% 51.46/7.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f88,plain,(
% 51.46/7.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f13])).
% 51.46/7.00  
% 51.46/7.00  fof(f14,axiom,(
% 51.46/7.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f89,plain,(
% 51.46/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f14])).
% 51.46/7.00  
% 51.46/7.00  fof(f15,axiom,(
% 51.46/7.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f90,plain,(
% 51.46/7.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f15])).
% 51.46/7.00  
% 51.46/7.00  fof(f118,plain,(
% 51.46/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.46/7.00    inference(definition_unfolding,[],[f89,f90])).
% 51.46/7.00  
% 51.46/7.00  fof(f119,plain,(
% 51.46/7.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.46/7.00    inference(definition_unfolding,[],[f88,f118])).
% 51.46/7.00  
% 51.46/7.00  fof(f120,plain,(
% 51.46/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.46/7.00    inference(definition_unfolding,[],[f87,f119])).
% 51.46/7.00  
% 51.46/7.00  fof(f121,plain,(
% 51.46/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.46/7.00    inference(definition_unfolding,[],[f86,f120])).
% 51.46/7.00  
% 51.46/7.00  fof(f122,plain,(
% 51.46/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.46/7.00    inference(definition_unfolding,[],[f85,f121])).
% 51.46/7.00  
% 51.46/7.00  fof(f123,plain,(
% 51.46/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.46/7.00    inference(definition_unfolding,[],[f91,f122])).
% 51.46/7.00  
% 51.46/7.00  fof(f125,plain,(
% 51.46/7.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.46/7.00    inference(definition_unfolding,[],[f82,f123])).
% 51.46/7.00  
% 51.46/7.00  fof(f25,axiom,(
% 51.46/7.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f49,plain,(
% 51.46/7.00    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 51.46/7.00    inference(ennf_transformation,[],[f25])).
% 51.46/7.00  
% 51.46/7.00  fof(f106,plain,(
% 51.46/7.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f49])).
% 51.46/7.00  
% 51.46/7.00  fof(f127,plain,(
% 51.46/7.00    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 51.46/7.00    inference(definition_unfolding,[],[f106,f123])).
% 51.46/7.00  
% 51.46/7.00  fof(f21,axiom,(
% 51.46/7.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f42,plain,(
% 51.46/7.00    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 51.46/7.00    inference(ennf_transformation,[],[f21])).
% 51.46/7.00  
% 51.46/7.00  fof(f43,plain,(
% 51.46/7.00    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 51.46/7.00    inference(flattening,[],[f42])).
% 51.46/7.00  
% 51.46/7.00  fof(f96,plain,(
% 51.46/7.00    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f43])).
% 51.46/7.00  
% 51.46/7.00  fof(f22,axiom,(
% 51.46/7.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f44,plain,(
% 51.46/7.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 51.46/7.00    inference(ennf_transformation,[],[f22])).
% 51.46/7.00  
% 51.46/7.00  fof(f97,plain,(
% 51.46/7.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f44])).
% 51.46/7.00  
% 51.46/7.00  fof(f3,axiom,(
% 51.46/7.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f62,plain,(
% 51.46/7.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.46/7.00    inference(nnf_transformation,[],[f3])).
% 51.46/7.00  
% 51.46/7.00  fof(f63,plain,(
% 51.46/7.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.46/7.00    inference(flattening,[],[f62])).
% 51.46/7.00  
% 51.46/7.00  fof(f78,plain,(
% 51.46/7.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f63])).
% 51.46/7.00  
% 51.46/7.00  fof(f31,conjecture,(
% 51.46/7.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f32,negated_conjecture,(
% 51.46/7.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 51.46/7.00    inference(negated_conjecture,[],[f31])).
% 51.46/7.00  
% 51.46/7.00  fof(f56,plain,(
% 51.46/7.00    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 51.46/7.00    inference(ennf_transformation,[],[f32])).
% 51.46/7.00  
% 51.46/7.00  fof(f57,plain,(
% 51.46/7.00    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 51.46/7.00    inference(flattening,[],[f56])).
% 51.46/7.00  
% 51.46/7.00  fof(f70,plain,(
% 51.46/7.00    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4) & r1_tarski(k10_relat_1(X0,sK4),sK3))) )),
% 51.46/7.00    introduced(choice_axiom,[])).
% 51.46/7.00  
% 51.46/7.00  fof(f69,plain,(
% 51.46/7.00    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2) & r1_tarski(k10_relat_1(sK2,X2),X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 51.46/7.00    introduced(choice_axiom,[])).
% 51.46/7.00  
% 51.46/7.00  fof(f71,plain,(
% 51.46/7.00    (k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) & r1_tarski(k10_relat_1(sK2,sK4),sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 51.46/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f70,f69])).
% 51.46/7.00  
% 51.46/7.00  fof(f117,plain,(
% 51.46/7.00    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)),
% 51.46/7.00    inference(cnf_transformation,[],[f71])).
% 51.46/7.00  
% 51.46/7.00  fof(f114,plain,(
% 51.46/7.00    v1_relat_1(sK2)),
% 51.46/7.00    inference(cnf_transformation,[],[f71])).
% 51.46/7.00  
% 51.46/7.00  fof(f17,axiom,(
% 51.46/7.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 51.46/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.46/7.00  
% 51.46/7.00  fof(f38,plain,(
% 51.46/7.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 51.46/7.00    inference(ennf_transformation,[],[f17])).
% 51.46/7.00  
% 51.46/7.00  fof(f92,plain,(
% 51.46/7.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 51.46/7.00    inference(cnf_transformation,[],[f38])).
% 51.46/7.00  
% 51.46/7.00  fof(f76,plain,(
% 51.46/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.46/7.00    inference(cnf_transformation,[],[f63])).
% 51.46/7.00  
% 51.46/7.00  fof(f132,plain,(
% 51.46/7.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.46/7.00    inference(equality_resolution,[],[f76])).
% 51.46/7.00  
% 51.46/7.00  fof(f116,plain,(
% 51.46/7.00    r1_tarski(k10_relat_1(sK2,sK4),sK3)),
% 51.46/7.00    inference(cnf_transformation,[],[f71])).
% 51.46/7.00  
% 51.46/7.00  cnf(c_10,plain,
% 51.46/7.00      ( ~ r1_tarski(X0,X1)
% 51.46/7.00      | ~ r1_tarski(X0,X2)
% 51.46/7.00      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 51.46/7.00      inference(cnf_transformation,[],[f125]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_185319,plain,
% 51.46/7.00      ( ~ r1_tarski(k10_relat_1(sK2,sK4),X0)
% 51.46/7.00      | ~ r1_tarski(k10_relat_1(sK2,sK4),X1)
% 51.46/7.00      | r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_10]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_189732,plain,
% 51.46/7.00      ( ~ r1_tarski(k10_relat_1(sK2,sK4),X0)
% 51.46/7.00      | ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4))
% 51.46/7.00      | r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK2,sK4)))) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_185319]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_199862,plain,
% 51.46/7.00      ( ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4))
% 51.46/7.00      | r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))))
% 51.46/7.00      | ~ r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_189732]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_626,plain,
% 51.46/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.46/7.00      theory(equality) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_1558,plain,
% 51.46/7.00      ( ~ r1_tarski(X0,X1)
% 51.46/7.00      | r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X1
% 51.46/7.00      | k10_relat_1(sK2,sK4) != X0 ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_626]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_26042,plain,
% 51.46/7.00      ( ~ r1_tarski(X0,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))))
% 51.46/7.00      | r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4)))
% 51.46/7.00      | k10_relat_1(sK2,sK4) != X0 ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_1558]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_55192,plain,
% 51.46/7.00      ( r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
% 51.46/7.00      | ~ r1_tarski(k10_relat_1(sK2,sK4),k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))))
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4)))
% 51.46/7.00      | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_26042]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_27,plain,
% 51.46/7.00      ( ~ v1_relat_1(X0)
% 51.46/7.00      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 51.46/7.00      inference(cnf_transformation,[],[f127]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_11446,plain,
% 51.46/7.00      ( ~ v1_relat_1(sK2)
% 51.46/7.00      | k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_27]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_624,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_1810,plain,
% 51.46/7.00      ( X0 != X1
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X1
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0 ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_624]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_4903,plain,
% 51.46/7.00      ( X0 != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_1810]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_11445,plain,
% 51.46/7.00      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4)))
% 51.46/7.00      | k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k10_relat_1(sK2,sK4))) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_4903]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_17,plain,
% 51.46/7.00      ( ~ r1_tarski(X0,X1)
% 51.46/7.00      | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
% 51.46/7.00      | ~ v1_relat_1(X0)
% 51.46/7.00      | ~ v1_relat_1(X1) ),
% 51.46/7.00      inference(cnf_transformation,[],[f96]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_10228,plain,
% 51.46/7.00      ( r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(X0,sK4))
% 51.46/7.00      | ~ r1_tarski(sK2,X0)
% 51.46/7.00      | ~ v1_relat_1(X0)
% 51.46/7.00      | ~ v1_relat_1(sK2) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_17]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_10232,plain,
% 51.46/7.00      ( r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4))
% 51.46/7.00      | ~ r1_tarski(sK2,sK2)
% 51.46/7.00      | ~ v1_relat_1(sK2) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_10228]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_18,plain,
% 51.46/7.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 51.46/7.00      inference(cnf_transformation,[],[f97]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_4764,plain,
% 51.46/7.00      ( r1_tarski(k7_relat_1(sK2,sK3),sK2) | ~ v1_relat_1(sK2) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_18]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_4,plain,
% 51.46/7.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 51.46/7.00      inference(cnf_transformation,[],[f78]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_34,negated_conjecture,
% 51.46/7.00      ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 51.46/7.00      inference(cnf_transformation,[],[f117]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_2553,plain,
% 51.46/7.00      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),k10_relat_1(sK2,sK4))
% 51.46/7.00      | ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4)) ),
% 51.46/7.00      inference(resolution,[status(thm)],[c_4,c_34]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_4379,plain,
% 51.46/7.00      ( ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
% 51.46/7.00      | ~ r1_tarski(k7_relat_1(sK2,sK3),sK2)
% 51.46/7.00      | ~ v1_relat_1(k7_relat_1(sK2,sK3))
% 51.46/7.00      | ~ v1_relat_1(sK2) ),
% 51.46/7.00      inference(resolution,[status(thm)],[c_17,c_2553]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_37,negated_conjecture,
% 51.46/7.00      ( v1_relat_1(sK2) ),
% 51.46/7.00      inference(cnf_transformation,[],[f114]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_13,plain,
% 51.46/7.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 51.46/7.00      inference(cnf_transformation,[],[f92]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_1774,plain,
% 51.46/7.00      ( v1_relat_1(k7_relat_1(sK2,sK3)) | ~ v1_relat_1(sK2) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_13]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_4382,plain,
% 51.46/7.00      ( ~ r1_tarski(k10_relat_1(sK2,sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
% 51.46/7.00      | ~ r1_tarski(k7_relat_1(sK2,sK3),sK2) ),
% 51.46/7.00      inference(global_propositional_subsumption,
% 51.46/7.00                [status(thm)],
% 51.46/7.00                [c_4379,c_37,c_1774]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_6,plain,
% 51.46/7.00      ( r1_tarski(X0,X0) ),
% 51.46/7.00      inference(cnf_transformation,[],[f132]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_2570,plain,
% 51.46/7.00      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4)) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_6]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_1794,plain,
% 51.46/7.00      ( ~ r1_tarski(X0,k10_relat_1(k7_relat_1(sK2,sK3),sK4))
% 51.46/7.00      | ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),X0)
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = X0 ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_4]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_2569,plain,
% 51.46/7.00      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK3),sK4),k10_relat_1(k7_relat_1(sK2,sK3),sK4))
% 51.46/7.00      | k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_1794]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_623,plain,( X0 = X0 ),theory(equality) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_1608,plain,
% 51.46/7.00      ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_623]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_117,plain,
% 51.46/7.00      ( r1_tarski(sK2,sK2) ),
% 51.46/7.00      inference(instantiation,[status(thm)],[c_6]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(c_35,negated_conjecture,
% 51.46/7.00      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
% 51.46/7.00      inference(cnf_transformation,[],[f116]) ).
% 51.46/7.00  
% 51.46/7.00  cnf(contradiction,plain,
% 51.46/7.00      ( $false ),
% 51.46/7.00      inference(minisat,
% 51.46/7.00                [status(thm)],
% 51.46/7.00                [c_199862,c_55192,c_11446,c_11445,c_10232,c_4764,c_4382,
% 51.46/7.00                 c_2570,c_2569,c_1608,c_117,c_35,c_37]) ).
% 51.46/7.00  
% 51.46/7.00  
% 51.46/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.46/7.00  
% 51.46/7.00  ------                               Statistics
% 51.46/7.00  
% 51.46/7.00  ------ Selected
% 51.46/7.00  
% 51.46/7.00  total_time:                             6.267
% 51.46/7.00  
%------------------------------------------------------------------------------
