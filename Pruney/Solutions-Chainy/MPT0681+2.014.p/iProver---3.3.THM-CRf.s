%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:21 EST 2020

% Result     : Theorem 15.62s
% Output     : CNFRefutation 15.62s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 212 expanded)
%              Number of clauses        :   68 (  82 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  274 ( 614 expanded)
%              Number of equality atoms :  100 ( 133 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
      & v2_funct_1(sK4)
      & r1_xboole_0(sK2,sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    & v2_funct_1(sK4)
    & r1_xboole_0(sK2,sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f29])).

fof(f47,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f46,f38,f38])).

fof(f50,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f51,plain,(
    ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_34727,plain,
    ( r1_xboole_0(k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6364,plain,
    ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),X0)
    | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))))
    | ~ r1_xboole_0(k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_34726,plain,
    ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))))
    | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_xboole_0)
    | ~ r1_xboole_0(k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6364])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_484,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_486,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_498,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_497,plain,
    ( r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1434,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_497])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_492,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2627,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1434,c_492])).

cnf(c_3447,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_tarski(sK2,sK3))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_486,c_2627])).

cnf(c_3735,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_484,c_3447])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_493,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1318,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_484,c_493])).

cnf(c_3742,plain,
    ( k9_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3735,c_1318])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_490,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_494,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_939,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_490,c_494])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_944,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_939,c_10,c_11])).

cnf(c_495,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1572,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
    | r1_xboole_0(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_492])).

cnf(c_28,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1739,plain,
    ( r1_xboole_0(X1,X0) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1572,c_28])).

cnf(c_1740,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1739])).

cnf(c_1747,plain,
    ( k7_relat_1(k6_relat_1(k1_xboole_0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_495,c_1740])).

cnf(c_1317,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_490,c_493])).

cnf(c_2229,plain,
    ( k9_relat_1(k6_relat_1(k1_xboole_0),X0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1747,c_1317])).

cnf(c_3916,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_944,c_2229])).

cnf(c_6868,plain,
    ( k9_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3742,c_3916])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_485,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_489,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1170,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_489])).

cnf(c_20,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2432,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_20,c_23])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_496,plain,
    ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2438,plain,
    ( r2_hidden(sK1(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)),k9_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))) = iProver_top
    | r1_xboole_0(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_496])).

cnf(c_6874,plain,
    ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_xboole_0) = iProver_top
    | r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6868,c_2438])).

cnf(c_6893,plain,
    ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_xboole_0)
    | r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6874])).

cnf(c_170,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_729,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | X0 != sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    | X1 != k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_858,plain,
    ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),X0)
    | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | X0 != k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))
    | sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) != sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_3816,plain,
    ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))))
    | sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) != sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    | k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))) != k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_1858,plain,
    ( k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) = k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_172,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_1057,plain,
    ( X0 != k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    | k1_setfam_1(X0) = k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_1857,plain,
    ( k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) != k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    | k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))) = k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_167,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_859,plain,
    ( sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_654,plain,
    ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
    | r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34727,c_34726,c_6893,c_3816,c_1858,c_1857,c_859,c_654,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:57:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.62/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.62/2.48  
% 15.62/2.48  ------  iProver source info
% 15.62/2.48  
% 15.62/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.62/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.62/2.48  git: non_committed_changes: false
% 15.62/2.48  git: last_make_outside_of_git: false
% 15.62/2.48  
% 15.62/2.48  ------ 
% 15.62/2.48  
% 15.62/2.48  ------ Input Options
% 15.62/2.48  
% 15.62/2.48  --out_options                           all
% 15.62/2.48  --tptp_safe_out                         true
% 15.62/2.48  --problem_path                          ""
% 15.62/2.48  --include_path                          ""
% 15.62/2.48  --clausifier                            res/vclausify_rel
% 15.62/2.48  --clausifier_options                    --mode clausify
% 15.62/2.48  --stdin                                 false
% 15.62/2.48  --stats_out                             sel
% 15.62/2.48  
% 15.62/2.48  ------ General Options
% 15.62/2.48  
% 15.62/2.48  --fof                                   false
% 15.62/2.48  --time_out_real                         604.99
% 15.62/2.48  --time_out_virtual                      -1.
% 15.62/2.48  --symbol_type_check                     false
% 15.62/2.48  --clausify_out                          false
% 15.62/2.48  --sig_cnt_out                           false
% 15.62/2.49  --trig_cnt_out                          false
% 15.62/2.49  --trig_cnt_out_tolerance                1.
% 15.62/2.49  --trig_cnt_out_sk_spl                   false
% 15.62/2.49  --abstr_cl_out                          false
% 15.62/2.49  
% 15.62/2.49  ------ Global Options
% 15.62/2.49  
% 15.62/2.49  --schedule                              none
% 15.62/2.49  --add_important_lit                     false
% 15.62/2.49  --prop_solver_per_cl                    1000
% 15.62/2.49  --min_unsat_core                        false
% 15.62/2.49  --soft_assumptions                      false
% 15.62/2.49  --soft_lemma_size                       3
% 15.62/2.49  --prop_impl_unit_size                   0
% 15.62/2.49  --prop_impl_unit                        []
% 15.62/2.49  --share_sel_clauses                     true
% 15.62/2.49  --reset_solvers                         false
% 15.62/2.49  --bc_imp_inh                            [conj_cone]
% 15.62/2.49  --conj_cone_tolerance                   3.
% 15.62/2.49  --extra_neg_conj                        none
% 15.62/2.49  --large_theory_mode                     true
% 15.62/2.49  --prolific_symb_bound                   200
% 15.62/2.49  --lt_threshold                          2000
% 15.62/2.49  --clause_weak_htbl                      true
% 15.62/2.49  --gc_record_bc_elim                     false
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing Options
% 15.62/2.49  
% 15.62/2.49  --preprocessing_flag                    true
% 15.62/2.49  --time_out_prep_mult                    0.1
% 15.62/2.49  --splitting_mode                        input
% 15.62/2.49  --splitting_grd                         true
% 15.62/2.49  --splitting_cvd                         false
% 15.62/2.49  --splitting_cvd_svl                     false
% 15.62/2.49  --splitting_nvd                         32
% 15.62/2.49  --sub_typing                            true
% 15.62/2.49  --prep_gs_sim                           false
% 15.62/2.49  --prep_unflatten                        true
% 15.62/2.49  --prep_res_sim                          true
% 15.62/2.49  --prep_upred                            true
% 15.62/2.49  --prep_sem_filter                       exhaustive
% 15.62/2.49  --prep_sem_filter_out                   false
% 15.62/2.49  --pred_elim                             false
% 15.62/2.49  --res_sim_input                         true
% 15.62/2.49  --eq_ax_congr_red                       true
% 15.62/2.49  --pure_diseq_elim                       true
% 15.62/2.49  --brand_transform                       false
% 15.62/2.49  --non_eq_to_eq                          false
% 15.62/2.49  --prep_def_merge                        true
% 15.62/2.49  --prep_def_merge_prop_impl              false
% 15.62/2.49  --prep_def_merge_mbd                    true
% 15.62/2.49  --prep_def_merge_tr_red                 false
% 15.62/2.49  --prep_def_merge_tr_cl                  false
% 15.62/2.49  --smt_preprocessing                     true
% 15.62/2.49  --smt_ac_axioms                         fast
% 15.62/2.49  --preprocessed_out                      false
% 15.62/2.49  --preprocessed_stats                    false
% 15.62/2.49  
% 15.62/2.49  ------ Abstraction refinement Options
% 15.62/2.49  
% 15.62/2.49  --abstr_ref                             []
% 15.62/2.49  --abstr_ref_prep                        false
% 15.62/2.49  --abstr_ref_until_sat                   false
% 15.62/2.49  --abstr_ref_sig_restrict                funpre
% 15.62/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.62/2.49  --abstr_ref_under                       []
% 15.62/2.49  
% 15.62/2.49  ------ SAT Options
% 15.62/2.49  
% 15.62/2.49  --sat_mode                              false
% 15.62/2.49  --sat_fm_restart_options                ""
% 15.62/2.49  --sat_gr_def                            false
% 15.62/2.49  --sat_epr_types                         true
% 15.62/2.49  --sat_non_cyclic_types                  false
% 15.62/2.49  --sat_finite_models                     false
% 15.62/2.49  --sat_fm_lemmas                         false
% 15.62/2.49  --sat_fm_prep                           false
% 15.62/2.49  --sat_fm_uc_incr                        true
% 15.62/2.49  --sat_out_model                         small
% 15.62/2.49  --sat_out_clauses                       false
% 15.62/2.49  
% 15.62/2.49  ------ QBF Options
% 15.62/2.49  
% 15.62/2.49  --qbf_mode                              false
% 15.62/2.49  --qbf_elim_univ                         false
% 15.62/2.49  --qbf_dom_inst                          none
% 15.62/2.49  --qbf_dom_pre_inst                      false
% 15.62/2.49  --qbf_sk_in                             false
% 15.62/2.49  --qbf_pred_elim                         true
% 15.62/2.49  --qbf_split                             512
% 15.62/2.49  
% 15.62/2.49  ------ BMC1 Options
% 15.62/2.49  
% 15.62/2.49  --bmc1_incremental                      false
% 15.62/2.49  --bmc1_axioms                           reachable_all
% 15.62/2.49  --bmc1_min_bound                        0
% 15.62/2.49  --bmc1_max_bound                        -1
% 15.62/2.49  --bmc1_max_bound_default                -1
% 15.62/2.49  --bmc1_symbol_reachability              true
% 15.62/2.49  --bmc1_property_lemmas                  false
% 15.62/2.49  --bmc1_k_induction                      false
% 15.62/2.49  --bmc1_non_equiv_states                 false
% 15.62/2.49  --bmc1_deadlock                         false
% 15.62/2.49  --bmc1_ucm                              false
% 15.62/2.49  --bmc1_add_unsat_core                   none
% 15.62/2.49  --bmc1_unsat_core_children              false
% 15.62/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.62/2.49  --bmc1_out_stat                         full
% 15.62/2.49  --bmc1_ground_init                      false
% 15.62/2.49  --bmc1_pre_inst_next_state              false
% 15.62/2.49  --bmc1_pre_inst_state                   false
% 15.62/2.49  --bmc1_pre_inst_reach_state             false
% 15.62/2.49  --bmc1_out_unsat_core                   false
% 15.62/2.49  --bmc1_aig_witness_out                  false
% 15.62/2.49  --bmc1_verbose                          false
% 15.62/2.49  --bmc1_dump_clauses_tptp                false
% 15.62/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.62/2.49  --bmc1_dump_file                        -
% 15.62/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.62/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.62/2.49  --bmc1_ucm_extend_mode                  1
% 15.62/2.49  --bmc1_ucm_init_mode                    2
% 15.62/2.49  --bmc1_ucm_cone_mode                    none
% 15.62/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.62/2.49  --bmc1_ucm_relax_model                  4
% 15.62/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.62/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.62/2.49  --bmc1_ucm_layered_model                none
% 15.62/2.49  --bmc1_ucm_max_lemma_size               10
% 15.62/2.49  
% 15.62/2.49  ------ AIG Options
% 15.62/2.49  
% 15.62/2.49  --aig_mode                              false
% 15.62/2.49  
% 15.62/2.49  ------ Instantiation Options
% 15.62/2.49  
% 15.62/2.49  --instantiation_flag                    true
% 15.62/2.49  --inst_sos_flag                         false
% 15.62/2.49  --inst_sos_phase                        true
% 15.62/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.62/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.62/2.49  --inst_lit_sel_side                     num_symb
% 15.62/2.49  --inst_solver_per_active                1400
% 15.62/2.49  --inst_solver_calls_frac                1.
% 15.62/2.49  --inst_passive_queue_type               priority_queues
% 15.62/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.62/2.49  --inst_passive_queues_freq              [25;2]
% 15.62/2.49  --inst_dismatching                      true
% 15.62/2.49  --inst_eager_unprocessed_to_passive     true
% 15.62/2.49  --inst_prop_sim_given                   true
% 15.62/2.49  --inst_prop_sim_new                     false
% 15.62/2.49  --inst_subs_new                         false
% 15.62/2.49  --inst_eq_res_simp                      false
% 15.62/2.49  --inst_subs_given                       false
% 15.62/2.49  --inst_orphan_elimination               true
% 15.62/2.49  --inst_learning_loop_flag               true
% 15.62/2.49  --inst_learning_start                   3000
% 15.62/2.49  --inst_learning_factor                  2
% 15.62/2.49  --inst_start_prop_sim_after_learn       3
% 15.62/2.49  --inst_sel_renew                        solver
% 15.62/2.49  --inst_lit_activity_flag                true
% 15.62/2.49  --inst_restr_to_given                   false
% 15.62/2.49  --inst_activity_threshold               500
% 15.62/2.49  --inst_out_proof                        true
% 15.62/2.49  
% 15.62/2.49  ------ Resolution Options
% 15.62/2.49  
% 15.62/2.49  --resolution_flag                       true
% 15.62/2.49  --res_lit_sel                           adaptive
% 15.62/2.49  --res_lit_sel_side                      none
% 15.62/2.49  --res_ordering                          kbo
% 15.62/2.49  --res_to_prop_solver                    active
% 15.62/2.49  --res_prop_simpl_new                    false
% 15.62/2.49  --res_prop_simpl_given                  true
% 15.62/2.49  --res_passive_queue_type                priority_queues
% 15.62/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.62/2.49  --res_passive_queues_freq               [15;5]
% 15.62/2.49  --res_forward_subs                      full
% 15.62/2.49  --res_backward_subs                     full
% 15.62/2.49  --res_forward_subs_resolution           true
% 15.62/2.49  --res_backward_subs_resolution          true
% 15.62/2.49  --res_orphan_elimination                true
% 15.62/2.49  --res_time_limit                        2.
% 15.62/2.49  --res_out_proof                         true
% 15.62/2.49  
% 15.62/2.49  ------ Superposition Options
% 15.62/2.49  
% 15.62/2.49  --superposition_flag                    true
% 15.62/2.49  --sup_passive_queue_type                priority_queues
% 15.62/2.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.62/2.49  --sup_passive_queues_freq               [1;4]
% 15.62/2.49  --demod_completeness_check              fast
% 15.62/2.49  --demod_use_ground                      true
% 15.62/2.49  --sup_to_prop_solver                    passive
% 15.62/2.49  --sup_prop_simpl_new                    true
% 15.62/2.49  --sup_prop_simpl_given                  true
% 15.62/2.49  --sup_fun_splitting                     false
% 15.62/2.49  --sup_smt_interval                      50000
% 15.62/2.49  
% 15.62/2.49  ------ Superposition Simplification Setup
% 15.62/2.49  
% 15.62/2.49  --sup_indices_passive                   []
% 15.62/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.62/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.49  --sup_full_bw                           [BwDemod]
% 15.62/2.49  --sup_immed_triv                        [TrivRules]
% 15.62/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.49  --sup_immed_bw_main                     []
% 15.62/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.62/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.49  
% 15.62/2.49  ------ Combination Options
% 15.62/2.49  
% 15.62/2.49  --comb_res_mult                         3
% 15.62/2.49  --comb_sup_mult                         2
% 15.62/2.49  --comb_inst_mult                        10
% 15.62/2.49  
% 15.62/2.49  ------ Debug Options
% 15.62/2.49  
% 15.62/2.49  --dbg_backtrace                         false
% 15.62/2.49  --dbg_dump_prop_clauses                 false
% 15.62/2.49  --dbg_dump_prop_clauses_file            -
% 15.62/2.49  --dbg_out_stat                          false
% 15.62/2.49  ------ Parsing...
% 15.62/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.62/2.49  ------ Proving...
% 15.62/2.49  ------ Problem Properties 
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  clauses                                 20
% 15.62/2.49  conjectures                             5
% 15.62/2.49  EPR                                     6
% 15.62/2.49  Horn                                    17
% 15.62/2.49  unary                                   11
% 15.62/2.49  binary                                  6
% 15.62/2.49  lits                                    33
% 15.62/2.49  lits eq                                 7
% 15.62/2.49  fd_pure                                 0
% 15.62/2.49  fd_pseudo                               0
% 15.62/2.49  fd_cond                                 0
% 15.62/2.49  fd_pseudo_cond                          0
% 15.62/2.49  AC symbols                              0
% 15.62/2.49  
% 15.62/2.49  ------ Input Options Time Limit: Unbounded
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  ------ 
% 15.62/2.49  Current options:
% 15.62/2.49  ------ 
% 15.62/2.49  
% 15.62/2.49  ------ Input Options
% 15.62/2.49  
% 15.62/2.49  --out_options                           all
% 15.62/2.49  --tptp_safe_out                         true
% 15.62/2.49  --problem_path                          ""
% 15.62/2.49  --include_path                          ""
% 15.62/2.49  --clausifier                            res/vclausify_rel
% 15.62/2.49  --clausifier_options                    --mode clausify
% 15.62/2.49  --stdin                                 false
% 15.62/2.49  --stats_out                             sel
% 15.62/2.49  
% 15.62/2.49  ------ General Options
% 15.62/2.49  
% 15.62/2.49  --fof                                   false
% 15.62/2.49  --time_out_real                         604.99
% 15.62/2.49  --time_out_virtual                      -1.
% 15.62/2.49  --symbol_type_check                     false
% 15.62/2.49  --clausify_out                          false
% 15.62/2.49  --sig_cnt_out                           false
% 15.62/2.49  --trig_cnt_out                          false
% 15.62/2.49  --trig_cnt_out_tolerance                1.
% 15.62/2.49  --trig_cnt_out_sk_spl                   false
% 15.62/2.49  --abstr_cl_out                          false
% 15.62/2.49  
% 15.62/2.49  ------ Global Options
% 15.62/2.49  
% 15.62/2.49  --schedule                              none
% 15.62/2.49  --add_important_lit                     false
% 15.62/2.49  --prop_solver_per_cl                    1000
% 15.62/2.49  --min_unsat_core                        false
% 15.62/2.49  --soft_assumptions                      false
% 15.62/2.49  --soft_lemma_size                       3
% 15.62/2.49  --prop_impl_unit_size                   0
% 15.62/2.49  --prop_impl_unit                        []
% 15.62/2.49  --share_sel_clauses                     true
% 15.62/2.49  --reset_solvers                         false
% 15.62/2.49  --bc_imp_inh                            [conj_cone]
% 15.62/2.49  --conj_cone_tolerance                   3.
% 15.62/2.49  --extra_neg_conj                        none
% 15.62/2.49  --large_theory_mode                     true
% 15.62/2.49  --prolific_symb_bound                   200
% 15.62/2.49  --lt_threshold                          2000
% 15.62/2.49  --clause_weak_htbl                      true
% 15.62/2.49  --gc_record_bc_elim                     false
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing Options
% 15.62/2.49  
% 15.62/2.49  --preprocessing_flag                    true
% 15.62/2.49  --time_out_prep_mult                    0.1
% 15.62/2.49  --splitting_mode                        input
% 15.62/2.49  --splitting_grd                         true
% 15.62/2.49  --splitting_cvd                         false
% 15.62/2.49  --splitting_cvd_svl                     false
% 15.62/2.49  --splitting_nvd                         32
% 15.62/2.49  --sub_typing                            true
% 15.62/2.49  --prep_gs_sim                           false
% 15.62/2.49  --prep_unflatten                        true
% 15.62/2.49  --prep_res_sim                          true
% 15.62/2.49  --prep_upred                            true
% 15.62/2.49  --prep_sem_filter                       exhaustive
% 15.62/2.49  --prep_sem_filter_out                   false
% 15.62/2.49  --pred_elim                             false
% 15.62/2.49  --res_sim_input                         true
% 15.62/2.49  --eq_ax_congr_red                       true
% 15.62/2.49  --pure_diseq_elim                       true
% 15.62/2.49  --brand_transform                       false
% 15.62/2.49  --non_eq_to_eq                          false
% 15.62/2.49  --prep_def_merge                        true
% 15.62/2.49  --prep_def_merge_prop_impl              false
% 15.62/2.49  --prep_def_merge_mbd                    true
% 15.62/2.49  --prep_def_merge_tr_red                 false
% 15.62/2.49  --prep_def_merge_tr_cl                  false
% 15.62/2.49  --smt_preprocessing                     true
% 15.62/2.49  --smt_ac_axioms                         fast
% 15.62/2.49  --preprocessed_out                      false
% 15.62/2.49  --preprocessed_stats                    false
% 15.62/2.49  
% 15.62/2.49  ------ Abstraction refinement Options
% 15.62/2.49  
% 15.62/2.49  --abstr_ref                             []
% 15.62/2.49  --abstr_ref_prep                        false
% 15.62/2.49  --abstr_ref_until_sat                   false
% 15.62/2.49  --abstr_ref_sig_restrict                funpre
% 15.62/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.62/2.49  --abstr_ref_under                       []
% 15.62/2.49  
% 15.62/2.49  ------ SAT Options
% 15.62/2.49  
% 15.62/2.49  --sat_mode                              false
% 15.62/2.49  --sat_fm_restart_options                ""
% 15.62/2.49  --sat_gr_def                            false
% 15.62/2.49  --sat_epr_types                         true
% 15.62/2.49  --sat_non_cyclic_types                  false
% 15.62/2.49  --sat_finite_models                     false
% 15.62/2.49  --sat_fm_lemmas                         false
% 15.62/2.49  --sat_fm_prep                           false
% 15.62/2.49  --sat_fm_uc_incr                        true
% 15.62/2.49  --sat_out_model                         small
% 15.62/2.49  --sat_out_clauses                       false
% 15.62/2.49  
% 15.62/2.49  ------ QBF Options
% 15.62/2.49  
% 15.62/2.49  --qbf_mode                              false
% 15.62/2.49  --qbf_elim_univ                         false
% 15.62/2.49  --qbf_dom_inst                          none
% 15.62/2.49  --qbf_dom_pre_inst                      false
% 15.62/2.49  --qbf_sk_in                             false
% 15.62/2.49  --qbf_pred_elim                         true
% 15.62/2.49  --qbf_split                             512
% 15.62/2.49  
% 15.62/2.49  ------ BMC1 Options
% 15.62/2.49  
% 15.62/2.49  --bmc1_incremental                      false
% 15.62/2.49  --bmc1_axioms                           reachable_all
% 15.62/2.49  --bmc1_min_bound                        0
% 15.62/2.49  --bmc1_max_bound                        -1
% 15.62/2.49  --bmc1_max_bound_default                -1
% 15.62/2.49  --bmc1_symbol_reachability              true
% 15.62/2.49  --bmc1_property_lemmas                  false
% 15.62/2.49  --bmc1_k_induction                      false
% 15.62/2.49  --bmc1_non_equiv_states                 false
% 15.62/2.49  --bmc1_deadlock                         false
% 15.62/2.49  --bmc1_ucm                              false
% 15.62/2.49  --bmc1_add_unsat_core                   none
% 15.62/2.49  --bmc1_unsat_core_children              false
% 15.62/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.62/2.49  --bmc1_out_stat                         full
% 15.62/2.49  --bmc1_ground_init                      false
% 15.62/2.49  --bmc1_pre_inst_next_state              false
% 15.62/2.49  --bmc1_pre_inst_state                   false
% 15.62/2.49  --bmc1_pre_inst_reach_state             false
% 15.62/2.49  --bmc1_out_unsat_core                   false
% 15.62/2.49  --bmc1_aig_witness_out                  false
% 15.62/2.49  --bmc1_verbose                          false
% 15.62/2.49  --bmc1_dump_clauses_tptp                false
% 15.62/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.62/2.49  --bmc1_dump_file                        -
% 15.62/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.62/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.62/2.49  --bmc1_ucm_extend_mode                  1
% 15.62/2.49  --bmc1_ucm_init_mode                    2
% 15.62/2.49  --bmc1_ucm_cone_mode                    none
% 15.62/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.62/2.49  --bmc1_ucm_relax_model                  4
% 15.62/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.62/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.62/2.49  --bmc1_ucm_layered_model                none
% 15.62/2.49  --bmc1_ucm_max_lemma_size               10
% 15.62/2.49  
% 15.62/2.49  ------ AIG Options
% 15.62/2.49  
% 15.62/2.49  --aig_mode                              false
% 15.62/2.49  
% 15.62/2.49  ------ Instantiation Options
% 15.62/2.49  
% 15.62/2.49  --instantiation_flag                    true
% 15.62/2.49  --inst_sos_flag                         false
% 15.62/2.49  --inst_sos_phase                        true
% 15.62/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.62/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.62/2.49  --inst_lit_sel_side                     num_symb
% 15.62/2.49  --inst_solver_per_active                1400
% 15.62/2.49  --inst_solver_calls_frac                1.
% 15.62/2.49  --inst_passive_queue_type               priority_queues
% 15.62/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.62/2.49  --inst_passive_queues_freq              [25;2]
% 15.62/2.49  --inst_dismatching                      true
% 15.62/2.49  --inst_eager_unprocessed_to_passive     true
% 15.62/2.49  --inst_prop_sim_given                   true
% 15.62/2.49  --inst_prop_sim_new                     false
% 15.62/2.49  --inst_subs_new                         false
% 15.62/2.49  --inst_eq_res_simp                      false
% 15.62/2.49  --inst_subs_given                       false
% 15.62/2.49  --inst_orphan_elimination               true
% 15.62/2.49  --inst_learning_loop_flag               true
% 15.62/2.49  --inst_learning_start                   3000
% 15.62/2.49  --inst_learning_factor                  2
% 15.62/2.49  --inst_start_prop_sim_after_learn       3
% 15.62/2.49  --inst_sel_renew                        solver
% 15.62/2.49  --inst_lit_activity_flag                true
% 15.62/2.49  --inst_restr_to_given                   false
% 15.62/2.49  --inst_activity_threshold               500
% 15.62/2.49  --inst_out_proof                        true
% 15.62/2.49  
% 15.62/2.49  ------ Resolution Options
% 15.62/2.49  
% 15.62/2.49  --resolution_flag                       true
% 15.62/2.49  --res_lit_sel                           adaptive
% 15.62/2.49  --res_lit_sel_side                      none
% 15.62/2.49  --res_ordering                          kbo
% 15.62/2.49  --res_to_prop_solver                    active
% 15.62/2.49  --res_prop_simpl_new                    false
% 15.62/2.49  --res_prop_simpl_given                  true
% 15.62/2.49  --res_passive_queue_type                priority_queues
% 15.62/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.62/2.49  --res_passive_queues_freq               [15;5]
% 15.62/2.49  --res_forward_subs                      full
% 15.62/2.49  --res_backward_subs                     full
% 15.62/2.49  --res_forward_subs_resolution           true
% 15.62/2.49  --res_backward_subs_resolution          true
% 15.62/2.49  --res_orphan_elimination                true
% 15.62/2.49  --res_time_limit                        2.
% 15.62/2.49  --res_out_proof                         true
% 15.62/2.49  
% 15.62/2.49  ------ Superposition Options
% 15.62/2.49  
% 15.62/2.49  --superposition_flag                    true
% 15.62/2.49  --sup_passive_queue_type                priority_queues
% 15.62/2.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.62/2.49  --sup_passive_queues_freq               [1;4]
% 15.62/2.49  --demod_completeness_check              fast
% 15.62/2.49  --demod_use_ground                      true
% 15.62/2.49  --sup_to_prop_solver                    passive
% 15.62/2.49  --sup_prop_simpl_new                    true
% 15.62/2.49  --sup_prop_simpl_given                  true
% 15.62/2.49  --sup_fun_splitting                     false
% 15.62/2.49  --sup_smt_interval                      50000
% 15.62/2.49  
% 15.62/2.49  ------ Superposition Simplification Setup
% 15.62/2.49  
% 15.62/2.49  --sup_indices_passive                   []
% 15.62/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.62/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.49  --sup_full_bw                           [BwDemod]
% 15.62/2.49  --sup_immed_triv                        [TrivRules]
% 15.62/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.49  --sup_immed_bw_main                     []
% 15.62/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.62/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.49  
% 15.62/2.49  ------ Combination Options
% 15.62/2.49  
% 15.62/2.49  --comb_res_mult                         3
% 15.62/2.49  --comb_sup_mult                         2
% 15.62/2.49  --comb_inst_mult                        10
% 15.62/2.49  
% 15.62/2.49  ------ Debug Options
% 15.62/2.49  
% 15.62/2.49  --dbg_backtrace                         false
% 15.62/2.49  --dbg_dump_prop_clauses                 false
% 15.62/2.49  --dbg_dump_prop_clauses_file            -
% 15.62/2.49  --dbg_out_stat                          false
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  ------ Proving...
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  % SZS status Theorem for theBenchmark.p
% 15.62/2.49  
% 15.62/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.62/2.49  
% 15.62/2.49  fof(f4,axiom,(
% 15.62/2.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f37,plain,(
% 15.62/2.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f4])).
% 15.62/2.49  
% 15.62/2.49  fof(f1,axiom,(
% 15.62/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f14,plain,(
% 15.62/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.62/2.49    inference(rectify,[],[f1])).
% 15.62/2.49  
% 15.62/2.49  fof(f16,plain,(
% 15.62/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.62/2.49    inference(ennf_transformation,[],[f14])).
% 15.62/2.49  
% 15.62/2.49  fof(f25,plain,(
% 15.62/2.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f26,plain,(
% 15.62/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).
% 15.62/2.49  
% 15.62/2.49  fof(f33,plain,(
% 15.62/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f26])).
% 15.62/2.49  
% 15.62/2.49  fof(f12,conjecture,(
% 15.62/2.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f13,negated_conjecture,(
% 15.62/2.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 15.62/2.49    inference(negated_conjecture,[],[f12])).
% 15.62/2.49  
% 15.62/2.49  fof(f23,plain,(
% 15.62/2.49    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 15.62/2.49    inference(ennf_transformation,[],[f13])).
% 15.62/2.49  
% 15.62/2.49  fof(f24,plain,(
% 15.62/2.49    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 15.62/2.49    inference(flattening,[],[f23])).
% 15.62/2.49  
% 15.62/2.49  fof(f29,plain,(
% 15.62/2.49    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v2_funct_1(sK4) & r1_xboole_0(sK2,sK3) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f30,plain,(
% 15.62/2.49    ~r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & v2_funct_1(sK4) & r1_xboole_0(sK2,sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 15.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f29])).
% 15.62/2.49  
% 15.62/2.49  fof(f47,plain,(
% 15.62/2.49    v1_relat_1(sK4)),
% 15.62/2.49    inference(cnf_transformation,[],[f30])).
% 15.62/2.49  
% 15.62/2.49  fof(f49,plain,(
% 15.62/2.49    r1_xboole_0(sK2,sK3)),
% 15.62/2.49    inference(cnf_transformation,[],[f30])).
% 15.62/2.49  
% 15.62/2.49  fof(f31,plain,(
% 15.62/2.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f26])).
% 15.62/2.49  
% 15.62/2.49  fof(f2,axiom,(
% 15.62/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f15,plain,(
% 15.62/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.62/2.49    inference(rectify,[],[f2])).
% 15.62/2.49  
% 15.62/2.49  fof(f17,plain,(
% 15.62/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.62/2.49    inference(ennf_transformation,[],[f15])).
% 15.62/2.49  
% 15.62/2.49  fof(f27,plain,(
% 15.62/2.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f28,plain,(
% 15.62/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f27])).
% 15.62/2.49  
% 15.62/2.49  fof(f35,plain,(
% 15.62/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.62/2.49    inference(cnf_transformation,[],[f28])).
% 15.62/2.49  
% 15.62/2.49  fof(f5,axiom,(
% 15.62/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f38,plain,(
% 15.62/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.62/2.49    inference(cnf_transformation,[],[f5])).
% 15.62/2.49  
% 15.62/2.49  fof(f52,plain,(
% 15.62/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 15.62/2.49    inference(definition_unfolding,[],[f35,f38])).
% 15.62/2.49  
% 15.62/2.49  fof(f8,axiom,(
% 15.62/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f20,plain,(
% 15.62/2.49    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.62/2.49    inference(ennf_transformation,[],[f8])).
% 15.62/2.49  
% 15.62/2.49  fof(f41,plain,(
% 15.62/2.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f20])).
% 15.62/2.49  
% 15.62/2.49  fof(f7,axiom,(
% 15.62/2.49    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f19,plain,(
% 15.62/2.49    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 15.62/2.49    inference(ennf_transformation,[],[f7])).
% 15.62/2.49  
% 15.62/2.49  fof(f40,plain,(
% 15.62/2.49    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f19])).
% 15.62/2.49  
% 15.62/2.49  fof(f10,axiom,(
% 15.62/2.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f44,plain,(
% 15.62/2.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 15.62/2.49    inference(cnf_transformation,[],[f10])).
% 15.62/2.49  
% 15.62/2.49  fof(f6,axiom,(
% 15.62/2.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f18,plain,(
% 15.62/2.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 15.62/2.49    inference(ennf_transformation,[],[f6])).
% 15.62/2.49  
% 15.62/2.49  fof(f39,plain,(
% 15.62/2.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f18])).
% 15.62/2.49  
% 15.62/2.49  fof(f9,axiom,(
% 15.62/2.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f43,plain,(
% 15.62/2.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 15.62/2.49    inference(cnf_transformation,[],[f9])).
% 15.62/2.49  
% 15.62/2.49  fof(f42,plain,(
% 15.62/2.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 15.62/2.49    inference(cnf_transformation,[],[f9])).
% 15.62/2.49  
% 15.62/2.49  fof(f48,plain,(
% 15.62/2.49    v1_funct_1(sK4)),
% 15.62/2.49    inference(cnf_transformation,[],[f30])).
% 15.62/2.49  
% 15.62/2.49  fof(f11,axiom,(
% 15.62/2.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 15.62/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f21,plain,(
% 15.62/2.49    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.62/2.49    inference(ennf_transformation,[],[f11])).
% 15.62/2.49  
% 15.62/2.49  fof(f22,plain,(
% 15.62/2.49    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.62/2.49    inference(flattening,[],[f21])).
% 15.62/2.49  
% 15.62/2.49  fof(f46,plain,(
% 15.62/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f22])).
% 15.62/2.49  
% 15.62/2.49  fof(f55,plain,(
% 15.62/2.49    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.62/2.49    inference(definition_unfolding,[],[f46,f38,f38])).
% 15.62/2.49  
% 15.62/2.49  fof(f50,plain,(
% 15.62/2.49    v2_funct_1(sK4)),
% 15.62/2.49    inference(cnf_transformation,[],[f30])).
% 15.62/2.49  
% 15.62/2.49  fof(f34,plain,(
% 15.62/2.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f28])).
% 15.62/2.49  
% 15.62/2.49  fof(f53,plain,(
% 15.62/2.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 15.62/2.49    inference(definition_unfolding,[],[f34,f38])).
% 15.62/2.49  
% 15.62/2.49  fof(f51,plain,(
% 15.62/2.49    ~r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),
% 15.62/2.49    inference(cnf_transformation,[],[f30])).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6,plain,
% 15.62/2.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 15.62/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_34727,plain,
% 15.62/2.49      ( r1_xboole_0(k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))),k1_xboole_0) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_0,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6364,plain,
% 15.62/2.49      ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),X0)
% 15.62/2.49      | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))))
% 15.62/2.49      | ~ r1_xboole_0(k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))),X0) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_34726,plain,
% 15.62/2.49      ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))))
% 15.62/2.49      | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_xboole_0)
% 15.62/2.49      | ~ r1_xboole_0(k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))),k1_xboole_0) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_6364]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_19,negated_conjecture,
% 15.62/2.49      ( v1_relat_1(sK4) ),
% 15.62/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_484,plain,
% 15.62/2.49      ( v1_relat_1(sK4) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_17,negated_conjecture,
% 15.62/2.49      ( r1_xboole_0(sK2,sK3) ),
% 15.62/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_486,plain,
% 15.62/2.49      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2,plain,
% 15.62/2.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f31]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_498,plain,
% 15.62/2.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.62/2.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_3,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 15.62/2.49      | ~ r1_xboole_0(X1,X2) ),
% 15.62/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_497,plain,
% 15.62/2.49      ( r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top
% 15.62/2.49      | r1_xboole_0(X1,X2) != iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1434,plain,
% 15.62/2.49      ( r1_xboole_0(X0,X1) != iProver_top
% 15.62/2.49      | r1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_498,c_497]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_9,plain,
% 15.62/2.49      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 15.62/2.49      | ~ v1_relat_1(X1)
% 15.62/2.49      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 15.62/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_492,plain,
% 15.62/2.49      ( k7_relat_1(X0,X1) = k1_xboole_0
% 15.62/2.49      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2627,plain,
% 15.62/2.49      ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
% 15.62/2.49      | r1_xboole_0(X1,X2) != iProver_top
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_1434,c_492]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_3447,plain,
% 15.62/2.49      ( k7_relat_1(X0,k1_setfam_1(k2_tarski(sK2,sK3))) = k1_xboole_0
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_486,c_2627]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_3735,plain,
% 15.62/2.49      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) = k1_xboole_0 ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_484,c_3447]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_8,plain,
% 15.62/2.49      ( ~ v1_relat_1(X0)
% 15.62/2.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_493,plain,
% 15.62/2.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1318,plain,
% 15.62/2.49      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_484,c_493]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_3742,plain,
% 15.62/2.49      ( k9_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) = k2_relat_1(k1_xboole_0) ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_3735,c_1318]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_13,plain,
% 15.62/2.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 15.62/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_490,plain,
% 15.62/2.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_7,plain,
% 15.62/2.49      ( ~ v1_relat_1(X0)
% 15.62/2.49      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 15.62/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_494,plain,
% 15.62/2.49      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_939,plain,
% 15.62/2.49      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_490,c_494]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_10,plain,
% 15.62/2.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 15.62/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_11,plain,
% 15.62/2.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 15.62/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_944,plain,
% 15.62/2.49      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 15.62/2.49      inference(light_normalisation,[status(thm)],[c_939,c_10,c_11]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_495,plain,
% 15.62/2.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1572,plain,
% 15.62/2.49      ( k7_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
% 15.62/2.49      | r1_xboole_0(X1,X0) != iProver_top
% 15.62/2.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_11,c_492]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_28,plain,
% 15.62/2.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1739,plain,
% 15.62/2.49      ( r1_xboole_0(X1,X0) != iProver_top
% 15.62/2.49      | k7_relat_1(k6_relat_1(X0),X1) = k1_xboole_0 ),
% 15.62/2.49      inference(global_propositional_subsumption,
% 15.62/2.49                [status(thm)],
% 15.62/2.49                [c_1572,c_28]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1740,plain,
% 15.62/2.49      ( k7_relat_1(k6_relat_1(X0),X1) = k1_xboole_0
% 15.62/2.49      | r1_xboole_0(X1,X0) != iProver_top ),
% 15.62/2.49      inference(renaming,[status(thm)],[c_1739]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1747,plain,
% 15.62/2.49      ( k7_relat_1(k6_relat_1(k1_xboole_0),X0) = k1_xboole_0 ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_495,c_1740]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1317,plain,
% 15.62/2.49      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_490,c_493]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2229,plain,
% 15.62/2.49      ( k9_relat_1(k6_relat_1(k1_xboole_0),X0) = k2_relat_1(k1_xboole_0) ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_1747,c_1317]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_3916,plain,
% 15.62/2.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_944,c_2229]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6868,plain,
% 15.62/2.49      ( k9_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) = k1_xboole_0 ),
% 15.62/2.49      inference(light_normalisation,[status(thm)],[c_3742,c_3916]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_18,negated_conjecture,
% 15.62/2.49      ( v1_funct_1(sK4) ),
% 15.62/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_485,plain,
% 15.62/2.49      ( v1_funct_1(sK4) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_14,plain,
% 15.62/2.49      ( ~ v1_funct_1(X0)
% 15.62/2.49      | ~ v2_funct_1(X0)
% 15.62/2.49      | ~ v1_relat_1(X0)
% 15.62/2.49      | k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 15.62/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_489,plain,
% 15.62/2.49      ( k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))) = k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 15.62/2.49      | v1_funct_1(X0) != iProver_top
% 15.62/2.49      | v2_funct_1(X0) != iProver_top
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1170,plain,
% 15.62/2.49      ( k1_setfam_1(k2_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))
% 15.62/2.49      | v2_funct_1(sK4) != iProver_top
% 15.62/2.49      | v1_relat_1(sK4) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_485,c_489]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_20,plain,
% 15.62/2.49      ( v1_relat_1(sK4) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_16,negated_conjecture,
% 15.62/2.49      ( v2_funct_1(sK4) ),
% 15.62/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_23,plain,
% 15.62/2.49      ( v2_funct_1(sK4) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2432,plain,
% 15.62/2.49      ( k1_setfam_1(k2_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))) = k9_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1))) ),
% 15.62/2.49      inference(global_propositional_subsumption,
% 15.62/2.49                [status(thm)],
% 15.62/2.49                [c_1170,c_20,c_23]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_4,plain,
% 15.62/2.49      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
% 15.62/2.49      | r1_xboole_0(X0,X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_496,plain,
% 15.62/2.49      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) = iProver_top
% 15.62/2.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2438,plain,
% 15.62/2.49      ( r2_hidden(sK1(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)),k9_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1)))) = iProver_top
% 15.62/2.49      | r1_xboole_0(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) = iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_2432,c_496]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6874,plain,
% 15.62/2.49      ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_xboole_0) = iProver_top
% 15.62/2.49      | r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_6868,c_2438]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6893,plain,
% 15.62/2.49      ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_xboole_0)
% 15.62/2.49      | r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 15.62/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_6874]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_170,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.62/2.49      theory(equality) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_729,plain,
% 15.62/2.49      ( r2_hidden(X0,X1)
% 15.62/2.49      | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 15.62/2.49      | X0 != sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
% 15.62/2.49      | X1 != k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_170]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_858,plain,
% 15.62/2.49      ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),X0)
% 15.62/2.49      | ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 15.62/2.49      | X0 != k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))
% 15.62/2.49      | sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) != sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_729]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_3816,plain,
% 15.62/2.49      ( ~ r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 15.62/2.49      | r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))))
% 15.62/2.49      | sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) != sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
% 15.62/2.49      | k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))) != k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_858]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1858,plain,
% 15.62/2.49      ( k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) = k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_172,plain,
% 15.62/2.49      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 15.62/2.49      theory(equality) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1057,plain,
% 15.62/2.49      ( X0 != k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
% 15.62/2.49      | k1_setfam_1(X0) = k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_172]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1857,plain,
% 15.62/2.49      ( k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)))) != k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
% 15.62/2.49      | k1_setfam_1(k2_relat_1(k6_relat_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))) = k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_1057]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_167,plain,( X0 = X0 ),theory(equality) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_859,plain,
% 15.62/2.49      ( sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_167]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_654,plain,
% 15.62/2.49      ( r2_hidden(sK1(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)),k1_setfam_1(k2_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))))
% 15.62/2.49      | r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_15,negated_conjecture,
% 15.62/2.49      ( ~ r1_xboole_0(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 15.62/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(contradiction,plain,
% 15.62/2.49      ( $false ),
% 15.62/2.49      inference(minisat,
% 15.62/2.49                [status(thm)],
% 15.62/2.49                [c_34727,c_34726,c_6893,c_3816,c_1858,c_1857,c_859,c_654,
% 15.62/2.49                 c_15]) ).
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.62/2.49  
% 15.62/2.49  ------                               Statistics
% 15.62/2.49  
% 15.62/2.49  ------ Selected
% 15.62/2.49  
% 15.62/2.49  total_time:                             1.822
% 15.62/2.49  
%------------------------------------------------------------------------------
