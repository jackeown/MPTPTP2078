%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:00 EST 2020

% Result     : Theorem 11.87s
% Output     : CNFRefutation 11.87s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 174 expanded)
%              Number of clauses        :   39 (  51 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  309 ( 580 expanded)
%              Number of equality atoms :  138 ( 218 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2)
      & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2)
    & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f29])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f38,f38])).

fof(f52,plain,(
    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f62,plain,(
    r2_hidden(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),sK3))) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
            & r2_hidden(sK1(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_527,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_528,plain,
    ( r2_hidden(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_972,plain,
    ( r2_hidden(sK2,k1_setfam_1(k1_enumset1(sK3,sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_528])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_536,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1483,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_536])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_529,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_533,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_534,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_594,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_529,c_533,c_534])).

cnf(c_2879,plain,
    ( k1_funct_1(k6_relat_1(sK3),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1483,c_594])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_532,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2029,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
    | r2_hidden(X2,X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_532])).

cnf(c_2362,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2029,c_533,c_534])).

cnf(c_2880,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK3),sK2)) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2362])).

cnf(c_2888,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2) = k1_funct_1(X0,sK2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2879,c_2880])).

cnf(c_48331,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) = k1_funct_1(sK4,sK2)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_527,c_2888])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_526,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_535,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1174,plain,
    ( k5_relat_1(k6_relat_1(X0),sK4) = k7_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_526,c_535])).

cnf(c_48334,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) = k1_funct_1(sK4,sK2)
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_48331,c_1174])).

cnf(c_249,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_789,plain,
    ( k1_funct_1(sK4,sK2) = k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_250,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_705,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != X0
    | k1_funct_1(sK4,sK2) != X0
    | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_788,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2)
    | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2)
    | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_17,negated_conjecture,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48334,c_789,c_788,c_17,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.87/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.87/1.98  
% 11.87/1.98  ------  iProver source info
% 11.87/1.98  
% 11.87/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.87/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.87/1.98  git: non_committed_changes: false
% 11.87/1.98  git: last_make_outside_of_git: false
% 11.87/1.98  
% 11.87/1.98  ------ 
% 11.87/1.98  
% 11.87/1.98  ------ Input Options
% 11.87/1.98  
% 11.87/1.98  --out_options                           all
% 11.87/1.98  --tptp_safe_out                         true
% 11.87/1.98  --problem_path                          ""
% 11.87/1.98  --include_path                          ""
% 11.87/1.98  --clausifier                            res/vclausify_rel
% 11.87/1.98  --clausifier_options                    --mode clausify
% 11.87/1.98  --stdin                                 false
% 11.87/1.98  --stats_out                             sel
% 11.87/1.98  
% 11.87/1.98  ------ General Options
% 11.87/1.98  
% 11.87/1.98  --fof                                   false
% 11.87/1.98  --time_out_real                         604.99
% 11.87/1.98  --time_out_virtual                      -1.
% 11.87/1.98  --symbol_type_check                     false
% 11.87/1.98  --clausify_out                          false
% 11.87/1.98  --sig_cnt_out                           false
% 11.87/1.98  --trig_cnt_out                          false
% 11.87/1.98  --trig_cnt_out_tolerance                1.
% 11.87/1.98  --trig_cnt_out_sk_spl                   false
% 11.87/1.98  --abstr_cl_out                          false
% 11.87/1.98  
% 11.87/1.98  ------ Global Options
% 11.87/1.98  
% 11.87/1.98  --schedule                              none
% 11.87/1.98  --add_important_lit                     false
% 11.87/1.98  --prop_solver_per_cl                    1000
% 11.87/1.98  --min_unsat_core                        false
% 11.87/1.98  --soft_assumptions                      false
% 11.87/1.98  --soft_lemma_size                       3
% 11.87/1.98  --prop_impl_unit_size                   0
% 11.87/1.98  --prop_impl_unit                        []
% 11.87/1.98  --share_sel_clauses                     true
% 11.87/1.98  --reset_solvers                         false
% 11.87/1.98  --bc_imp_inh                            [conj_cone]
% 11.87/1.98  --conj_cone_tolerance                   3.
% 11.87/1.98  --extra_neg_conj                        none
% 11.87/1.98  --large_theory_mode                     true
% 11.87/1.98  --prolific_symb_bound                   200
% 11.87/1.98  --lt_threshold                          2000
% 11.87/1.98  --clause_weak_htbl                      true
% 11.87/1.98  --gc_record_bc_elim                     false
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing Options
% 11.87/1.98  
% 11.87/1.98  --preprocessing_flag                    true
% 11.87/1.98  --time_out_prep_mult                    0.1
% 11.87/1.98  --splitting_mode                        input
% 11.87/1.98  --splitting_grd                         true
% 11.87/1.98  --splitting_cvd                         false
% 11.87/1.98  --splitting_cvd_svl                     false
% 11.87/1.98  --splitting_nvd                         32
% 11.87/1.98  --sub_typing                            true
% 11.87/1.98  --prep_gs_sim                           false
% 11.87/1.98  --prep_unflatten                        true
% 11.87/1.98  --prep_res_sim                          true
% 11.87/1.98  --prep_upred                            true
% 11.87/1.98  --prep_sem_filter                       exhaustive
% 11.87/1.98  --prep_sem_filter_out                   false
% 11.87/1.98  --pred_elim                             false
% 11.87/1.98  --res_sim_input                         true
% 11.87/1.98  --eq_ax_congr_red                       true
% 11.87/1.98  --pure_diseq_elim                       true
% 11.87/1.98  --brand_transform                       false
% 11.87/1.98  --non_eq_to_eq                          false
% 11.87/1.98  --prep_def_merge                        true
% 11.87/1.98  --prep_def_merge_prop_impl              false
% 11.87/1.98  --prep_def_merge_mbd                    true
% 11.87/1.98  --prep_def_merge_tr_red                 false
% 11.87/1.98  --prep_def_merge_tr_cl                  false
% 11.87/1.98  --smt_preprocessing                     true
% 11.87/1.98  --smt_ac_axioms                         fast
% 11.87/1.98  --preprocessed_out                      false
% 11.87/1.98  --preprocessed_stats                    false
% 11.87/1.98  
% 11.87/1.98  ------ Abstraction refinement Options
% 11.87/1.98  
% 11.87/1.98  --abstr_ref                             []
% 11.87/1.98  --abstr_ref_prep                        false
% 11.87/1.98  --abstr_ref_until_sat                   false
% 11.87/1.98  --abstr_ref_sig_restrict                funpre
% 11.87/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.87/1.98  --abstr_ref_under                       []
% 11.87/1.98  
% 11.87/1.98  ------ SAT Options
% 11.87/1.98  
% 11.87/1.98  --sat_mode                              false
% 11.87/1.98  --sat_fm_restart_options                ""
% 11.87/1.98  --sat_gr_def                            false
% 11.87/1.98  --sat_epr_types                         true
% 11.87/1.98  --sat_non_cyclic_types                  false
% 11.87/1.98  --sat_finite_models                     false
% 11.87/1.98  --sat_fm_lemmas                         false
% 11.87/1.98  --sat_fm_prep                           false
% 11.87/1.98  --sat_fm_uc_incr                        true
% 11.87/1.98  --sat_out_model                         small
% 11.87/1.98  --sat_out_clauses                       false
% 11.87/1.98  
% 11.87/1.98  ------ QBF Options
% 11.87/1.98  
% 11.87/1.98  --qbf_mode                              false
% 11.87/1.98  --qbf_elim_univ                         false
% 11.87/1.98  --qbf_dom_inst                          none
% 11.87/1.98  --qbf_dom_pre_inst                      false
% 11.87/1.98  --qbf_sk_in                             false
% 11.87/1.98  --qbf_pred_elim                         true
% 11.87/1.98  --qbf_split                             512
% 11.87/1.98  
% 11.87/1.98  ------ BMC1 Options
% 11.87/1.98  
% 11.87/1.98  --bmc1_incremental                      false
% 11.87/1.98  --bmc1_axioms                           reachable_all
% 11.87/1.98  --bmc1_min_bound                        0
% 11.87/1.98  --bmc1_max_bound                        -1
% 11.87/1.98  --bmc1_max_bound_default                -1
% 11.87/1.98  --bmc1_symbol_reachability              true
% 11.87/1.98  --bmc1_property_lemmas                  false
% 11.87/1.98  --bmc1_k_induction                      false
% 11.87/1.98  --bmc1_non_equiv_states                 false
% 11.87/1.98  --bmc1_deadlock                         false
% 11.87/1.98  --bmc1_ucm                              false
% 11.87/1.98  --bmc1_add_unsat_core                   none
% 11.87/1.98  --bmc1_unsat_core_children              false
% 11.87/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.87/1.98  --bmc1_out_stat                         full
% 11.87/1.98  --bmc1_ground_init                      false
% 11.87/1.98  --bmc1_pre_inst_next_state              false
% 11.87/1.98  --bmc1_pre_inst_state                   false
% 11.87/1.98  --bmc1_pre_inst_reach_state             false
% 11.87/1.98  --bmc1_out_unsat_core                   false
% 11.87/1.98  --bmc1_aig_witness_out                  false
% 11.87/1.98  --bmc1_verbose                          false
% 11.87/1.98  --bmc1_dump_clauses_tptp                false
% 11.87/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.87/1.98  --bmc1_dump_file                        -
% 11.87/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.87/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.87/1.98  --bmc1_ucm_extend_mode                  1
% 11.87/1.98  --bmc1_ucm_init_mode                    2
% 11.87/1.98  --bmc1_ucm_cone_mode                    none
% 11.87/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.87/1.98  --bmc1_ucm_relax_model                  4
% 11.87/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.87/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.87/1.98  --bmc1_ucm_layered_model                none
% 11.87/1.98  --bmc1_ucm_max_lemma_size               10
% 11.87/1.98  
% 11.87/1.98  ------ AIG Options
% 11.87/1.98  
% 11.87/1.98  --aig_mode                              false
% 11.87/1.98  
% 11.87/1.98  ------ Instantiation Options
% 11.87/1.98  
% 11.87/1.98  --instantiation_flag                    true
% 11.87/1.98  --inst_sos_flag                         false
% 11.87/1.98  --inst_sos_phase                        true
% 11.87/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel_side                     num_symb
% 11.87/1.98  --inst_solver_per_active                1400
% 11.87/1.98  --inst_solver_calls_frac                1.
% 11.87/1.98  --inst_passive_queue_type               priority_queues
% 11.87/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.87/1.98  --inst_passive_queues_freq              [25;2]
% 11.87/1.98  --inst_dismatching                      true
% 11.87/1.98  --inst_eager_unprocessed_to_passive     true
% 11.87/1.98  --inst_prop_sim_given                   true
% 11.87/1.98  --inst_prop_sim_new                     false
% 11.87/1.98  --inst_subs_new                         false
% 11.87/1.98  --inst_eq_res_simp                      false
% 11.87/1.98  --inst_subs_given                       false
% 11.87/1.98  --inst_orphan_elimination               true
% 11.87/1.98  --inst_learning_loop_flag               true
% 11.87/1.98  --inst_learning_start                   3000
% 11.87/1.98  --inst_learning_factor                  2
% 11.87/1.98  --inst_start_prop_sim_after_learn       3
% 11.87/1.98  --inst_sel_renew                        solver
% 11.87/1.98  --inst_lit_activity_flag                true
% 11.87/1.98  --inst_restr_to_given                   false
% 11.87/1.98  --inst_activity_threshold               500
% 11.87/1.98  --inst_out_proof                        true
% 11.87/1.98  
% 11.87/1.98  ------ Resolution Options
% 11.87/1.98  
% 11.87/1.98  --resolution_flag                       true
% 11.87/1.98  --res_lit_sel                           adaptive
% 11.87/1.98  --res_lit_sel_side                      none
% 11.87/1.98  --res_ordering                          kbo
% 11.87/1.98  --res_to_prop_solver                    active
% 11.87/1.98  --res_prop_simpl_new                    false
% 11.87/1.98  --res_prop_simpl_given                  true
% 11.87/1.98  --res_passive_queue_type                priority_queues
% 11.87/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.87/1.98  --res_passive_queues_freq               [15;5]
% 11.87/1.98  --res_forward_subs                      full
% 11.87/1.98  --res_backward_subs                     full
% 11.87/1.98  --res_forward_subs_resolution           true
% 11.87/1.98  --res_backward_subs_resolution          true
% 11.87/1.98  --res_orphan_elimination                true
% 11.87/1.98  --res_time_limit                        2.
% 11.87/1.98  --res_out_proof                         true
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Options
% 11.87/1.98  
% 11.87/1.98  --superposition_flag                    true
% 11.87/1.98  --sup_passive_queue_type                priority_queues
% 11.87/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.87/1.98  --sup_passive_queues_freq               [1;4]
% 11.87/1.98  --demod_completeness_check              fast
% 11.87/1.98  --demod_use_ground                      true
% 11.87/1.98  --sup_to_prop_solver                    passive
% 11.87/1.98  --sup_prop_simpl_new                    true
% 11.87/1.98  --sup_prop_simpl_given                  true
% 11.87/1.98  --sup_fun_splitting                     false
% 11.87/1.98  --sup_smt_interval                      50000
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Simplification Setup
% 11.87/1.98  
% 11.87/1.98  --sup_indices_passive                   []
% 11.87/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.87/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_full_bw                           [BwDemod]
% 11.87/1.98  --sup_immed_triv                        [TrivRules]
% 11.87/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_immed_bw_main                     []
% 11.87/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.87/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.87/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.87/1.98  
% 11.87/1.98  ------ Combination Options
% 11.87/1.98  
% 11.87/1.98  --comb_res_mult                         3
% 11.87/1.98  --comb_sup_mult                         2
% 11.87/1.98  --comb_inst_mult                        10
% 11.87/1.98  
% 11.87/1.98  ------ Debug Options
% 11.87/1.98  
% 11.87/1.98  --dbg_backtrace                         false
% 11.87/1.98  --dbg_dump_prop_clauses                 false
% 11.87/1.98  --dbg_dump_prop_clauses_file            -
% 11.87/1.98  --dbg_out_stat                          false
% 11.87/1.98  ------ Parsing...
% 11.87/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/1.98  ------ Proving...
% 11.87/1.98  ------ Problem Properties 
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  clauses                                 20
% 11.87/1.98  conjectures                             4
% 11.87/1.98  EPR                                     2
% 11.87/1.98  Horn                                    17
% 11.87/1.98  unary                                   9
% 11.87/1.98  binary                                  3
% 11.87/1.98  lits                                    46
% 11.87/1.98  lits eq                                 13
% 11.87/1.98  fd_pure                                 0
% 11.87/1.98  fd_pseudo                               0
% 11.87/1.98  fd_cond                                 0
% 11.87/1.98  fd_pseudo_cond                          3
% 11.87/1.98  AC symbols                              0
% 11.87/1.98  
% 11.87/1.98  ------ Input Options Time Limit: Unbounded
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  ------ 
% 11.87/1.98  Current options:
% 11.87/1.98  ------ 
% 11.87/1.98  
% 11.87/1.98  ------ Input Options
% 11.87/1.98  
% 11.87/1.98  --out_options                           all
% 11.87/1.98  --tptp_safe_out                         true
% 11.87/1.98  --problem_path                          ""
% 11.87/1.98  --include_path                          ""
% 11.87/1.98  --clausifier                            res/vclausify_rel
% 11.87/1.98  --clausifier_options                    --mode clausify
% 11.87/1.98  --stdin                                 false
% 11.87/1.98  --stats_out                             sel
% 11.87/1.98  
% 11.87/1.98  ------ General Options
% 11.87/1.98  
% 11.87/1.98  --fof                                   false
% 11.87/1.98  --time_out_real                         604.99
% 11.87/1.98  --time_out_virtual                      -1.
% 11.87/1.98  --symbol_type_check                     false
% 11.87/1.98  --clausify_out                          false
% 11.87/1.98  --sig_cnt_out                           false
% 11.87/1.98  --trig_cnt_out                          false
% 11.87/1.98  --trig_cnt_out_tolerance                1.
% 11.87/1.98  --trig_cnt_out_sk_spl                   false
% 11.87/1.98  --abstr_cl_out                          false
% 11.87/1.98  
% 11.87/1.98  ------ Global Options
% 11.87/1.98  
% 11.87/1.98  --schedule                              none
% 11.87/1.98  --add_important_lit                     false
% 11.87/1.98  --prop_solver_per_cl                    1000
% 11.87/1.98  --min_unsat_core                        false
% 11.87/1.98  --soft_assumptions                      false
% 11.87/1.98  --soft_lemma_size                       3
% 11.87/1.98  --prop_impl_unit_size                   0
% 11.87/1.98  --prop_impl_unit                        []
% 11.87/1.98  --share_sel_clauses                     true
% 11.87/1.98  --reset_solvers                         false
% 11.87/1.98  --bc_imp_inh                            [conj_cone]
% 11.87/1.98  --conj_cone_tolerance                   3.
% 11.87/1.98  --extra_neg_conj                        none
% 11.87/1.98  --large_theory_mode                     true
% 11.87/1.98  --prolific_symb_bound                   200
% 11.87/1.98  --lt_threshold                          2000
% 11.87/1.98  --clause_weak_htbl                      true
% 11.87/1.98  --gc_record_bc_elim                     false
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing Options
% 11.87/1.98  
% 11.87/1.98  --preprocessing_flag                    true
% 11.87/1.98  --time_out_prep_mult                    0.1
% 11.87/1.98  --splitting_mode                        input
% 11.87/1.98  --splitting_grd                         true
% 11.87/1.98  --splitting_cvd                         false
% 11.87/1.98  --splitting_cvd_svl                     false
% 11.87/1.98  --splitting_nvd                         32
% 11.87/1.98  --sub_typing                            true
% 11.87/1.98  --prep_gs_sim                           false
% 11.87/1.98  --prep_unflatten                        true
% 11.87/1.98  --prep_res_sim                          true
% 11.87/1.98  --prep_upred                            true
% 11.87/1.98  --prep_sem_filter                       exhaustive
% 11.87/1.98  --prep_sem_filter_out                   false
% 11.87/1.98  --pred_elim                             false
% 11.87/1.98  --res_sim_input                         true
% 11.87/1.98  --eq_ax_congr_red                       true
% 11.87/1.98  --pure_diseq_elim                       true
% 11.87/1.98  --brand_transform                       false
% 11.87/1.98  --non_eq_to_eq                          false
% 11.87/1.98  --prep_def_merge                        true
% 11.87/1.98  --prep_def_merge_prop_impl              false
% 11.87/1.98  --prep_def_merge_mbd                    true
% 11.87/1.98  --prep_def_merge_tr_red                 false
% 11.87/1.98  --prep_def_merge_tr_cl                  false
% 11.87/1.98  --smt_preprocessing                     true
% 11.87/1.98  --smt_ac_axioms                         fast
% 11.87/1.98  --preprocessed_out                      false
% 11.87/1.98  --preprocessed_stats                    false
% 11.87/1.98  
% 11.87/1.98  ------ Abstraction refinement Options
% 11.87/1.98  
% 11.87/1.98  --abstr_ref                             []
% 11.87/1.98  --abstr_ref_prep                        false
% 11.87/1.98  --abstr_ref_until_sat                   false
% 11.87/1.98  --abstr_ref_sig_restrict                funpre
% 11.87/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.87/1.98  --abstr_ref_under                       []
% 11.87/1.98  
% 11.87/1.98  ------ SAT Options
% 11.87/1.98  
% 11.87/1.98  --sat_mode                              false
% 11.87/1.98  --sat_fm_restart_options                ""
% 11.87/1.98  --sat_gr_def                            false
% 11.87/1.98  --sat_epr_types                         true
% 11.87/1.98  --sat_non_cyclic_types                  false
% 11.87/1.98  --sat_finite_models                     false
% 11.87/1.98  --sat_fm_lemmas                         false
% 11.87/1.98  --sat_fm_prep                           false
% 11.87/1.98  --sat_fm_uc_incr                        true
% 11.87/1.98  --sat_out_model                         small
% 11.87/1.98  --sat_out_clauses                       false
% 11.87/1.98  
% 11.87/1.98  ------ QBF Options
% 11.87/1.98  
% 11.87/1.98  --qbf_mode                              false
% 11.87/1.98  --qbf_elim_univ                         false
% 11.87/1.98  --qbf_dom_inst                          none
% 11.87/1.98  --qbf_dom_pre_inst                      false
% 11.87/1.98  --qbf_sk_in                             false
% 11.87/1.98  --qbf_pred_elim                         true
% 11.87/1.98  --qbf_split                             512
% 11.87/1.98  
% 11.87/1.98  ------ BMC1 Options
% 11.87/1.98  
% 11.87/1.98  --bmc1_incremental                      false
% 11.87/1.98  --bmc1_axioms                           reachable_all
% 11.87/1.98  --bmc1_min_bound                        0
% 11.87/1.98  --bmc1_max_bound                        -1
% 11.87/1.98  --bmc1_max_bound_default                -1
% 11.87/1.98  --bmc1_symbol_reachability              true
% 11.87/1.98  --bmc1_property_lemmas                  false
% 11.87/1.98  --bmc1_k_induction                      false
% 11.87/1.98  --bmc1_non_equiv_states                 false
% 11.87/1.98  --bmc1_deadlock                         false
% 11.87/1.98  --bmc1_ucm                              false
% 11.87/1.98  --bmc1_add_unsat_core                   none
% 11.87/1.98  --bmc1_unsat_core_children              false
% 11.87/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.87/1.98  --bmc1_out_stat                         full
% 11.87/1.98  --bmc1_ground_init                      false
% 11.87/1.98  --bmc1_pre_inst_next_state              false
% 11.87/1.98  --bmc1_pre_inst_state                   false
% 11.87/1.98  --bmc1_pre_inst_reach_state             false
% 11.87/1.98  --bmc1_out_unsat_core                   false
% 11.87/1.98  --bmc1_aig_witness_out                  false
% 11.87/1.98  --bmc1_verbose                          false
% 11.87/1.98  --bmc1_dump_clauses_tptp                false
% 11.87/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.87/1.98  --bmc1_dump_file                        -
% 11.87/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.87/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.87/1.98  --bmc1_ucm_extend_mode                  1
% 11.87/1.98  --bmc1_ucm_init_mode                    2
% 11.87/1.98  --bmc1_ucm_cone_mode                    none
% 11.87/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.87/1.98  --bmc1_ucm_relax_model                  4
% 11.87/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.87/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.87/1.98  --bmc1_ucm_layered_model                none
% 11.87/1.98  --bmc1_ucm_max_lemma_size               10
% 11.87/1.98  
% 11.87/1.98  ------ AIG Options
% 11.87/1.98  
% 11.87/1.98  --aig_mode                              false
% 11.87/1.98  
% 11.87/1.98  ------ Instantiation Options
% 11.87/1.98  
% 11.87/1.98  --instantiation_flag                    true
% 11.87/1.98  --inst_sos_flag                         false
% 11.87/1.98  --inst_sos_phase                        true
% 11.87/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel_side                     num_symb
% 11.87/1.98  --inst_solver_per_active                1400
% 11.87/1.98  --inst_solver_calls_frac                1.
% 11.87/1.98  --inst_passive_queue_type               priority_queues
% 11.87/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.87/1.98  --inst_passive_queues_freq              [25;2]
% 11.87/1.98  --inst_dismatching                      true
% 11.87/1.98  --inst_eager_unprocessed_to_passive     true
% 11.87/1.98  --inst_prop_sim_given                   true
% 11.87/1.98  --inst_prop_sim_new                     false
% 11.87/1.98  --inst_subs_new                         false
% 11.87/1.98  --inst_eq_res_simp                      false
% 11.87/1.98  --inst_subs_given                       false
% 11.87/1.98  --inst_orphan_elimination               true
% 11.87/1.98  --inst_learning_loop_flag               true
% 11.87/1.98  --inst_learning_start                   3000
% 11.87/1.98  --inst_learning_factor                  2
% 11.87/1.98  --inst_start_prop_sim_after_learn       3
% 11.87/1.98  --inst_sel_renew                        solver
% 11.87/1.98  --inst_lit_activity_flag                true
% 11.87/1.98  --inst_restr_to_given                   false
% 11.87/1.98  --inst_activity_threshold               500
% 11.87/1.98  --inst_out_proof                        true
% 11.87/1.98  
% 11.87/1.98  ------ Resolution Options
% 11.87/1.98  
% 11.87/1.98  --resolution_flag                       true
% 11.87/1.98  --res_lit_sel                           adaptive
% 11.87/1.98  --res_lit_sel_side                      none
% 11.87/1.98  --res_ordering                          kbo
% 11.87/1.98  --res_to_prop_solver                    active
% 11.87/1.98  --res_prop_simpl_new                    false
% 11.87/1.98  --res_prop_simpl_given                  true
% 11.87/1.98  --res_passive_queue_type                priority_queues
% 11.87/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.87/1.98  --res_passive_queues_freq               [15;5]
% 11.87/1.98  --res_forward_subs                      full
% 11.87/1.98  --res_backward_subs                     full
% 11.87/1.98  --res_forward_subs_resolution           true
% 11.87/1.98  --res_backward_subs_resolution          true
% 11.87/1.98  --res_orphan_elimination                true
% 11.87/1.98  --res_time_limit                        2.
% 11.87/1.98  --res_out_proof                         true
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Options
% 11.87/1.98  
% 11.87/1.98  --superposition_flag                    true
% 11.87/1.98  --sup_passive_queue_type                priority_queues
% 11.87/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.87/1.98  --sup_passive_queues_freq               [1;4]
% 11.87/1.98  --demod_completeness_check              fast
% 11.87/1.98  --demod_use_ground                      true
% 11.87/1.98  --sup_to_prop_solver                    passive
% 11.87/1.98  --sup_prop_simpl_new                    true
% 11.87/1.98  --sup_prop_simpl_given                  true
% 11.87/1.98  --sup_fun_splitting                     false
% 11.87/1.98  --sup_smt_interval                      50000
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Simplification Setup
% 11.87/1.98  
% 11.87/1.98  --sup_indices_passive                   []
% 11.87/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.87/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_full_bw                           [BwDemod]
% 11.87/1.98  --sup_immed_triv                        [TrivRules]
% 11.87/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_immed_bw_main                     []
% 11.87/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.87/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.87/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.87/1.98  
% 11.87/1.98  ------ Combination Options
% 11.87/1.98  
% 11.87/1.98  --comb_res_mult                         3
% 11.87/1.98  --comb_sup_mult                         2
% 11.87/1.98  --comb_inst_mult                        10
% 11.87/1.98  
% 11.87/1.98  ------ Debug Options
% 11.87/1.98  
% 11.87/1.98  --dbg_backtrace                         false
% 11.87/1.98  --dbg_dump_prop_clauses                 false
% 11.87/1.98  --dbg_dump_prop_clauses_file            -
% 11.87/1.98  --dbg_out_stat                          false
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  ------ Proving...
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  % SZS status Theorem for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  fof(f10,conjecture,(
% 11.87/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f11,negated_conjecture,(
% 11.87/1.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 11.87/1.98    inference(negated_conjecture,[],[f10])).
% 11.87/1.98  
% 11.87/1.98  fof(f17,plain,(
% 11.87/1.98    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.87/1.98    inference(ennf_transformation,[],[f11])).
% 11.87/1.98  
% 11.87/1.98  fof(f18,plain,(
% 11.87/1.98    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.87/1.98    inference(flattening,[],[f17])).
% 11.87/1.98  
% 11.87/1.98  fof(f29,plain,(
% 11.87/1.98    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f30,plain,(
% 11.87/1.98    k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f29])).
% 11.87/1.98  
% 11.87/1.98  fof(f51,plain,(
% 11.87/1.98    v1_funct_1(sK4)),
% 11.87/1.98    inference(cnf_transformation,[],[f30])).
% 11.87/1.98  
% 11.87/1.98  fof(f2,axiom,(
% 11.87/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f37,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f2])).
% 11.87/1.98  
% 11.87/1.98  fof(f3,axiom,(
% 11.87/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f38,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f3])).
% 11.87/1.98  
% 11.87/1.98  fof(f61,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 11.87/1.98    inference(definition_unfolding,[],[f37,f38,f38])).
% 11.87/1.98  
% 11.87/1.98  fof(f52,plain,(
% 11.87/1.98    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))),
% 11.87/1.98    inference(cnf_transformation,[],[f30])).
% 11.87/1.98  
% 11.87/1.98  fof(f4,axiom,(
% 11.87/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f39,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.87/1.98    inference(cnf_transformation,[],[f4])).
% 11.87/1.98  
% 11.87/1.98  fof(f54,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 11.87/1.98    inference(definition_unfolding,[],[f39,f38])).
% 11.87/1.98  
% 11.87/1.98  fof(f62,plain,(
% 11.87/1.98    r2_hidden(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),sK3)))),
% 11.87/1.98    inference(definition_unfolding,[],[f52,f54])).
% 11.87/1.98  
% 11.87/1.98  fof(f1,axiom,(
% 11.87/1.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f19,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(nnf_transformation,[],[f1])).
% 11.87/1.98  
% 11.87/1.98  fof(f20,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(flattening,[],[f19])).
% 11.87/1.98  
% 11.87/1.98  fof(f21,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(rectify,[],[f20])).
% 11.87/1.98  
% 11.87/1.98  fof(f22,plain,(
% 11.87/1.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f23,plain,(
% 11.87/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 11.87/1.98  
% 11.87/1.98  fof(f31,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.87/1.98    inference(cnf_transformation,[],[f23])).
% 11.87/1.98  
% 11.87/1.98  fof(f60,plain,(
% 11.87/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2) )),
% 11.87/1.98    inference(definition_unfolding,[],[f31,f54])).
% 11.87/1.98  
% 11.87/1.98  fof(f65,plain,(
% 11.87/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 11.87/1.98    inference(equality_resolution,[],[f60])).
% 11.87/1.98  
% 11.87/1.98  fof(f9,axiom,(
% 11.87/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f15,plain,(
% 11.87/1.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.87/1.98    inference(ennf_transformation,[],[f9])).
% 11.87/1.98  
% 11.87/1.98  fof(f16,plain,(
% 11.87/1.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.87/1.98    inference(flattening,[],[f15])).
% 11.87/1.98  
% 11.87/1.98  fof(f24,plain,(
% 11.87/1.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.87/1.98    inference(nnf_transformation,[],[f16])).
% 11.87/1.98  
% 11.87/1.98  fof(f25,plain,(
% 11.87/1.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.87/1.98    inference(flattening,[],[f24])).
% 11.87/1.98  
% 11.87/1.98  fof(f26,plain,(
% 11.87/1.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.87/1.98    inference(rectify,[],[f25])).
% 11.87/1.98  
% 11.87/1.98  fof(f27,plain,(
% 11.87/1.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f28,plain,(
% 11.87/1.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 11.87/1.98  
% 11.87/1.98  fof(f47,plain,(
% 11.87/1.98    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0) | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f28])).
% 11.87/1.98  
% 11.87/1.98  fof(f68,plain,(
% 11.87/1.98    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 11.87/1.98    inference(equality_resolution,[],[f47])).
% 11.87/1.98  
% 11.87/1.98  fof(f7,axiom,(
% 11.87/1.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f43,plain,(
% 11.87/1.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.87/1.98    inference(cnf_transformation,[],[f7])).
% 11.87/1.98  
% 11.87/1.98  fof(f44,plain,(
% 11.87/1.98    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 11.87/1.98    inference(cnf_transformation,[],[f7])).
% 11.87/1.98  
% 11.87/1.98  fof(f5,axiom,(
% 11.87/1.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f40,plain,(
% 11.87/1.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.87/1.98    inference(cnf_transformation,[],[f5])).
% 11.87/1.98  
% 11.87/1.98  fof(f8,axiom,(
% 11.87/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f13,plain,(
% 11.87/1.98    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.87/1.98    inference(ennf_transformation,[],[f8])).
% 11.87/1.98  
% 11.87/1.98  fof(f14,plain,(
% 11.87/1.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.87/1.98    inference(flattening,[],[f13])).
% 11.87/1.98  
% 11.87/1.98  fof(f45,plain,(
% 11.87/1.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f14])).
% 11.87/1.98  
% 11.87/1.98  fof(f50,plain,(
% 11.87/1.98    v1_relat_1(sK4)),
% 11.87/1.98    inference(cnf_transformation,[],[f30])).
% 11.87/1.98  
% 11.87/1.98  fof(f6,axiom,(
% 11.87/1.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 11.87/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f12,plain,(
% 11.87/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 11.87/1.98    inference(ennf_transformation,[],[f6])).
% 11.87/1.98  
% 11.87/1.98  fof(f42,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f12])).
% 11.87/1.98  
% 11.87/1.98  fof(f53,plain,(
% 11.87/1.98    k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2)),
% 11.87/1.98    inference(cnf_transformation,[],[f30])).
% 11.87/1.98  
% 11.87/1.98  cnf(c_19,negated_conjecture,
% 11.87/1.98      ( v1_funct_1(sK4) ),
% 11.87/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_527,plain,
% 11.87/1.98      ( v1_funct_1(sK4) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_6,plain,
% 11.87/1.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 11.87/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_18,negated_conjecture,
% 11.87/1.98      ( r2_hidden(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),sK3))) ),
% 11.87/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_528,plain,
% 11.87/1.98      ( r2_hidden(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),sK3))) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_972,plain,
% 11.87/1.98      ( r2_hidden(sK2,k1_setfam_1(k1_enumset1(sK3,sK3,k1_relat_1(sK4)))) = iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_6,c_528]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_5,plain,
% 11.87/1.98      ( r2_hidden(X0,X1)
% 11.87/1.98      | ~ r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 11.87/1.98      inference(cnf_transformation,[],[f65]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_536,plain,
% 11.87/1.98      ( r2_hidden(X0,X1) = iProver_top
% 11.87/1.98      | r2_hidden(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1483,plain,
% 11.87/1.98      ( r2_hidden(sK2,sK3) = iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_972,c_536]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_15,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,X1)
% 11.87/1.98      | ~ v1_funct_1(k6_relat_1(X1))
% 11.87/1.98      | ~ v1_relat_1(k6_relat_1(X1))
% 11.87/1.98      | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
% 11.87/1.98      inference(cnf_transformation,[],[f68]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_529,plain,
% 11.87/1.98      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 11.87/1.98      | r2_hidden(X1,X0) != iProver_top
% 11.87/1.98      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 11.87/1.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_11,plain,
% 11.87/1.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_533,plain,
% 11.87/1.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_10,plain,
% 11.87/1.98      ( v1_funct_1(k6_relat_1(X0)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_534,plain,
% 11.87/1.98      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_594,plain,
% 11.87/1.98      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 11.87/1.98      | r2_hidden(X1,X0) != iProver_top ),
% 11.87/1.98      inference(forward_subsumption_resolution,
% 11.87/1.98                [status(thm)],
% 11.87/1.98                [c_529,c_533,c_534]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2879,plain,
% 11.87/1.98      ( k1_funct_1(k6_relat_1(sK3),sK2) = sK2 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1483,c_594]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_8,plain,
% 11.87/1.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.87/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_12,plain,
% 11.87/1.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.87/1.98      | ~ v1_funct_1(X2)
% 11.87/1.98      | ~ v1_funct_1(X1)
% 11.87/1.98      | ~ v1_relat_1(X1)
% 11.87/1.98      | ~ v1_relat_1(X2)
% 11.87/1.98      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_532,plain,
% 11.87/1.98      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 11.87/1.98      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 11.87/1.98      | v1_funct_1(X1) != iProver_top
% 11.87/1.98      | v1_funct_1(X0) != iProver_top
% 11.87/1.98      | v1_relat_1(X0) != iProver_top
% 11.87/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2029,plain,
% 11.87/1.98      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
% 11.87/1.98      | r2_hidden(X2,X1) != iProver_top
% 11.87/1.98      | v1_funct_1(X0) != iProver_top
% 11.87/1.98      | v1_funct_1(k6_relat_1(X1)) != iProver_top
% 11.87/1.98      | v1_relat_1(X0) != iProver_top
% 11.87/1.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_8,c_532]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2362,plain,
% 11.87/1.98      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
% 11.87/1.98      | r2_hidden(X2,X0) != iProver_top
% 11.87/1.98      | v1_funct_1(X1) != iProver_top
% 11.87/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.87/1.98      inference(forward_subsumption_resolution,
% 11.87/1.98                [status(thm)],
% 11.87/1.98                [c_2029,c_533,c_534]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2880,plain,
% 11.87/1.98      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK3),sK2)) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2)
% 11.87/1.98      | v1_funct_1(X0) != iProver_top
% 11.87/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1483,c_2362]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2888,plain,
% 11.87/1.98      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2) = k1_funct_1(X0,sK2)
% 11.87/1.98      | v1_funct_1(X0) != iProver_top
% 11.87/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_2879,c_2880]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_48331,plain,
% 11.87/1.98      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) = k1_funct_1(sK4,sK2)
% 11.87/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_527,c_2888]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_20,negated_conjecture,
% 11.87/1.98      ( v1_relat_1(sK4) ),
% 11.87/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_526,plain,
% 11.87/1.98      ( v1_relat_1(sK4) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_9,plain,
% 11.87/1.98      ( ~ v1_relat_1(X0)
% 11.87/1.98      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 11.87/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_535,plain,
% 11.87/1.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 11.87/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1174,plain,
% 11.87/1.98      ( k5_relat_1(k6_relat_1(X0),sK4) = k7_relat_1(sK4,X0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_526,c_535]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_48334,plain,
% 11.87/1.98      ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) = k1_funct_1(sK4,sK2)
% 11.87/1.98      | v1_relat_1(sK4) != iProver_top ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_48331,c_1174]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_249,plain,( X0 = X0 ),theory(equality) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_789,plain,
% 11.87/1.98      ( k1_funct_1(sK4,sK2) = k1_funct_1(sK4,sK2) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_249]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_250,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_705,plain,
% 11.87/1.98      ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != X0
% 11.87/1.98      | k1_funct_1(sK4,sK2) != X0
% 11.87/1.98      | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_250]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_788,plain,
% 11.87/1.98      ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2)
% 11.87/1.98      | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2)
% 11.87/1.98      | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_705]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_17,negated_conjecture,
% 11.87/1.98      ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
% 11.87/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_21,plain,
% 11.87/1.98      ( v1_relat_1(sK4) = iProver_top ),
% 11.87/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(contradiction,plain,
% 11.87/1.98      ( $false ),
% 11.87/1.98      inference(minisat,[status(thm)],[c_48334,c_789,c_788,c_17,c_21]) ).
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  ------                               Statistics
% 11.87/1.98  
% 11.87/1.98  ------ Selected
% 11.87/1.98  
% 11.87/1.98  total_time:                             1.491
% 11.87/1.98  
%------------------------------------------------------------------------------
